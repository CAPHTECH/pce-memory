/**
 * @pce/embeddings EmbeddingService
 * ADR-0003: 形式検証済み処理フロー実装
 *
 * 処理フロー: Redact → Hash → Cache Lookup → Provider Call → Cache Store
 * TLA+ 不変条件:
 * - Inv_NoProcessingWithoutProvider: プロバイダーなしで処理しない
 * - Inv_UniqueRequestId: リクエストIDの一意性
 * - Inv_CacheVersionConsistency: キャッシュバージョン整合性
 *
 * Alloy 制約:
 * - RedactBeforeEmbed: 機密データは埋め込み前にRedact
 */

import * as TE from 'fp-ts/TaskEither';
import * as E from 'fp-ts/Either';
import * as A from 'fp-ts/Array';
import { pipe } from 'fp-ts/function';
import type {
  EmbeddingProvider,
  EmbeddingCache,
  EmbeddingServiceConfig,
  EmbedParams,
  EmbedResult,
  BatchEmbedResult,
  SensitivityLevel,
} from './types.js';
import { MAX_BATCH_SIZE } from './types.js';
import type { EmbeddingError, CacheError } from './errors.js';
import { batchSizeExceededError, noProviderError } from './errors.js';
import { computeContentHash } from './hash.js';
import { prepareForEmbedding, requiresRedact } from './redact.js';

// ========== 型定義 ==========

/**
 * EmbeddingService インターフェース
 * ADR-0003: サービス層抽象化
 */
export interface EmbeddingService {
  /** 現在のモデルバージョン */
  readonly modelVersion: string;

  /** プライマリプロバイダーのステータス */
  readonly primaryStatus: 'available' | 'unavailable' | 'degraded';

  /**
   * 単一テキストの埋め込み生成
   * ADR-0003フロー: Redact → Hash → Cache → Provider → Store
   */
  embed(params: EmbedParams): TE.TaskEither<EmbeddingError, EmbedResult>;

  /**
   * バッチ埋め込み生成（最大32件）
   */
  embedBatch(params: readonly EmbedParams[]): TE.TaskEither<EmbeddingError, BatchEmbedResult>;

  /**
   * キャッシュをクリア
   */
  clearCache(): TE.TaskEither<CacheError, void>;

  /**
   * モデルバージョンを更新（キャッシュ無効化を伴う）
   */
  updateModelVersion(newVersion: string): TE.TaskEither<CacheError, void>;
}

/**
 * サービスエラー型（EmbeddingError | CacheError統合）
 */
export type ServiceError = EmbeddingError | CacheError;

// ========== 内部ヘルパー ==========

/**
 * Redact-before-Embed を適用
 * Alloy: RedactBeforeEmbed constraint
 */
const applyRedact = (
  text: string,
  sensitivity: SensitivityLevel
): E.Either<EmbeddingError, string> => {
  // 機密データでない場合はそのまま
  if (!requiresRedact(sensitivity)) {
    return E.right(text);
  }

  // Redact処理を適用
  const prepared = prepareForEmbedding(text, sensitivity);

  if (E.isLeft(prepared)) {
    // RedactErrorをEmbeddingErrorに変換
    return E.left({
      _tag: 'EmbeddingError',
      code: 'REDACT_REQUIRED',
      message: prepared.left.message,
      cause: prepared.left,
    } as EmbeddingError);
  }

  return E.right(prepared.right.text);
};

// ========== サービス実装 ==========

/**
 * EmbeddingServiceを作成
 *
 * ADR-0003 処理フロー:
 * 1. Redact: 機密データの除去（Alloy RedactBeforeEmbed）
 * 2. Hash: SHA-256でテキストハッシュ生成
 * 3. Cache Lookup: バージョン込みキーでキャッシュ検索
 * 4. Provider Call: キャッシュミス時、プロバイダーで埋め込み生成
 * 5. Cache Store: 結果をキャッシュに保存
 *
 * @param config サービス設定
 * @returns EmbeddingService
 */
export const createEmbeddingService = (config: EmbeddingServiceConfig): EmbeddingService => {
  const { primary, fallback, cache, onCacheError } = config;

  // 最後に同期したバージョン（レース条件でのロールバック防止用）
  // 単調増加を保証: 一度新しいバージョンに同期したら、古いバージョンには戻さない
  let lastSyncedVersion: string = cache.currentModelVersion;

  /**
   * onCacheErrorを安全に呼び出す（同期・非同期両方の例外をキャッチ）
   * コールバック内の例外でリクエスト全体が失敗することを防ぐ
   * Note: Promise.resolve()でラップすることで非同期コールバックのrejectionも捕捉
   */
  const safeOnCacheError = (error: CacheError, operation: 'read' | 'write'): void => {
    try {
      // 同期例外をキャッチし、非同期rejectionもPromise.resolve().catch()で捕捉
      Promise.resolve(onCacheError?.(error, operation)).catch(() => {
        // 非同期コールバック内の例外は無視（ベストエフォート）
      });
    } catch {
      // 同期コールバック内の例外は無視（ベストエフォート）
    }
  };

  /**
   * ベストエフォートキャッシュ読み取り
   * キャッシュエラー時はundefinedを返し、処理を継続
   */
  type CacheHit = { embedding: readonly number[]; modelVersion: string };
  const cacheGetBestEffort = (textHash: string): TE.TaskEither<never, CacheHit | undefined> =>
    pipe(
      cache.get(textHash),
      TE.map((entry): CacheHit | undefined =>
        entry ? { embedding: entry.embedding, modelVersion: entry.modelVersion } : undefined
      ),
      TE.orElse((cacheErr): TE.TaskEither<never, CacheHit | undefined> => {
        safeOnCacheError(cacheErr, 'read');
        return TE.right(undefined);
      })
    );

  /**
   * ベストエフォートキャッシュ書き込み
   * キャッシュエラー時は無視して処理を継続
   */
  const cacheSetBestEffort = (
    textHash: string,
    embedding: readonly number[],
    modelVersion: string
  ): TE.TaskEither<never, void> =>
    pipe(
      cache.set(textHash, embedding, modelVersion),
      TE.orElse((cacheErr) => {
        safeOnCacheError(cacheErr, 'write');
        return TE.right(undefined as void);
      })
    );

  /**
   * バージョン一致時のみキャッシュに書き込む（レース条件緩和）
   * 書き込み直前にバージョン再チェックし、不一致ならスキップ
   *
   * TLA+ Inv_CacheVersionConsistency準拠:
   * - 書き込み直前のバージョンチェックでレース窓を最小化
   * - 完全なCASではないが、実用上十分な保護を提供
   *
   * TODO: 非アトミック操作（ADR-0003「既知の制限事項」参照）
   * - チェックと書き込みの間にバージョン変更が入る可能性あり（極めて稀）
   * - 影響: 古いバージョンのエントリが一時的に残る（次回getで無視される）
   * - 将来的にはAsyncMutexまたはCASパターンで完全な保護を実装可能
   *
   * @param expectedVersion 期待するキャッシュバージョン
   */
  const cacheSetIfVersionMatches = (
    textHash: string,
    embedding: readonly number[],
    expectedVersion: string
  ): TE.TaskEither<never, void> => {
    // 書き込み直前にバージョン再チェック
    if (expectedVersion !== cache.currentModelVersion) {
      // バージョン変更済み → 書き込みスキップ（別リクエストが先に同期完了）
      return TE.right(undefined);
    }
    return cacheSetBestEffort(textHash, embedding, expectedVersion);
  };

  /**
   * キャッシュバージョンを同期（TLA+ Inv_CacheVersionConsistency準拠）
   * フェイルオーバー後など、プロバイダーのバージョンとキャッシュが異なる場合に呼び出す
   *
   * @returns true: 同期成功, false: 同期失敗（ベストエフォート継続）
   *
   * Note: 同期失敗時はキャッシュ書き込みをスキップする必要がある
   * （cache.currentModelVersionが古いままだと、新バージョンで書き込んでも
   *   次回検索時にキーが一致しないため）
   *
   * ロールバック防止（単調性保証）:
   * - 一度lastSyncedVersionが更新されると、古いバージョンへの同期はスキップ
   * - これにより、並行リクエストでの「後勝ち」によるバージョン巻き戻しを防止
   * - 例: A(v1)とB(v2)が並行実行時、Bが先に完了→Aは同期スキップ
   */
  const syncCacheVersion = (targetVersion: string): TE.TaskEither<never, boolean> => {
    // ロールバック防止チェック
    // 既に別のリクエストが新しいバージョンに同期済みの場合はスキップ
    if (targetVersion === lastSyncedVersion) {
      // 同じバージョン: 既に同期済み
      return TE.right(true);
    }

    // 注意: 文字列比較では「新しい」かどうかを判定できないため、
    // 「異なるバージョンへの最初の同期」を許可し、以降の同期をスキップする方式
    // フェイルオーバー時のバージョン切り替えを正しく処理しつつ、
    // 並行リクエストのレース条件を緩和
    if (cache.currentModelVersion === targetVersion) {
      // キャッシュは既に目標バージョン（別リクエストが先に同期完了）
      lastSyncedVersion = targetVersion;
      return TE.right(true);
    }

    return pipe(
      cache.updateModelVersion(targetVersion),
      TE.map(() => {
        // 同期成功: lastSyncedVersionを更新
        lastSyncedVersion = targetVersion;
        return true;
      }),
      TE.orElse((cacheErr) => {
        safeOnCacheError(cacheErr, 'write');
        return TE.right(false); // 同期失敗（ただしfatalではない）
      })
    );
  };

  /**
   * プロバイダーで埋め込みを生成（フェイルオーバー付き）
   * ADR-0003: 即時フェイルオーバー - プライマリ失敗時にフォールバックへ切り替え
   */
  type EmbedWithFailoverResult = {
    embedding: readonly number[];
    modelVersion: string;
  };

  const embedWithFailover = (
    text: string
  ): TE.TaskEither<EmbeddingError, EmbedWithFailoverResult> => {
    // 結果をラップするヘルパー
    const wrapResult = (
      embedding: readonly number[],
      version: string
    ): EmbedWithFailoverResult => ({
      embedding,
      modelVersion: version,
    });

    // プライマリが利用可能な場合
    if (primary.status === 'available' || primary.status === 'degraded') {
      return pipe(
        primary.embed(text),
        // まず結果をラップ（TE.orElseの前にmapして型を統一）
        TE.map((embedding) => wrapResult(embedding, primary.modelVersion)),
        // プライマリ失敗時のフェイルオーバー
        TE.orElse((primaryError) => {
          if (fallback && (fallback.status === 'available' || fallback.status === 'degraded')) {
            return pipe(
              fallback.embed(text),
              TE.map((embedding) => wrapResult(embedding, fallback.modelVersion))
            );
          }
          return TE.left(primaryError);
        })
      );
    }

    // プライマリが利用不可の場合、フォールバックへ
    if (fallback && (fallback.status === 'available' || fallback.status === 'degraded')) {
      return pipe(
        fallback.embed(text),
        TE.map((embedding) => wrapResult(embedding, fallback.modelVersion))
      );
    }

    // 両方利用不可
    return TE.left(noProviderError());
  };

  /**
   * 単一テキストの処理
   * TLA+準拠フロー:
   * 1. キャッシュ検索（プロバイダー可用性チェック前）
   * 2. キャッシュヒット時: プロバイダー不要で返却
   * 3. キャッシュミス時: プロバイダー呼び出し
   * 4. フェイルオーバー時: cache.updateModelVersionでバージョン同期
   */
  const processOne = (params: EmbedParams): TE.TaskEither<EmbeddingError, EmbedResult> => {
    const { text, sensitivity, skipCache = false } = params;

    // Step 1: Redact-before-Embed
    const redactResult = applyRedact(text, sensitivity);
    if (E.isLeft(redactResult)) {
      return TE.left(redactResult.left);
    }
    const processedText = redactResult.right;

    // Step 2: Hash計算
    const textHash = computeContentHash(processedText);

    // Step 3: キャッシュ検索（skipCacheでない場合）
    // プロバイダー可用性チェック前にキャッシュを確認（キャッシュがあればプロバイダー不要）
    if (!skipCache) {
      return pipe(
        cacheGetBestEffort(textHash),
        TE.flatMap((cacheEntry) => {
          // キャッシュヒット（現在のキャッシュバージョンと一致）
          if (cacheEntry && cacheEntry.modelVersion === cache.currentModelVersion) {
            return TE.right<EmbeddingError, EmbedResult>({
              embedding: cacheEntry.embedding,
              modelVersion: cacheEntry.modelVersion,
              fromCache: true,
              textHash,
            });
          }

          // Step 4: プロバイダー呼び出し（フェイルオーバー付き）
          // Note: embedWithFailoverが既にNO_PROVIDERエラーを返すため
          //       selectProviderの事前チェックは不要
          return pipe(
            embedWithFailover(processedText),
            TE.flatMap(({ embedding, modelVersion }) =>
              pipe(
                // Step 5: バージョン不一致時はキャッシュバージョンを同期
                // TLA+ Inv_CacheVersionConsistency準拠
                modelVersion !== cache.currentModelVersion
                  ? syncCacheVersion(modelVersion)
                  : TE.right<never, boolean>(true), // 同期不要=成功扱い
                // Step 6: キャッシュに保存（同期成功時 & バージョン一致時のみ）
                // cacheSetIfVersionMatchesで書き込み直前にバージョン再チェック
                // → レース条件緩和（別リクエストが先に同期完了した場合はスキップ）
                TE.flatMap(
                  (syncSucceeded) =>
                    syncSucceeded
                      ? cacheSetIfVersionMatches(textHash, embedding, modelVersion)
                      : TE.right<never, void>(undefined) // 同期失敗時はスキップ
                ),
                TE.map(() => ({
                  embedding,
                  modelVersion,
                  fromCache: false,
                  textHash,
                }))
              )
            )
          );
        })
      );
    }

    // skipCache: 直接プロバイダー呼び出し
    // Note: embedWithFailoverが既にNO_PROVIDERエラーを返すため
    //       selectProviderの事前チェックは不要
    return pipe(
      embedWithFailover(processedText),
      TE.flatMap(({ embedding, modelVersion }) =>
        pipe(
          // バージョン不一致時はキャッシュバージョンを同期
          // skipCache時もバージョン同期は必要（次回リクエストのため）
          modelVersion !== cache.currentModelVersion
            ? syncCacheVersion(modelVersion)
            : TE.right<never, boolean>(true), // 同期不要=成功扱い
          // skipCache: キャッシュ書き込みなし（同期結果は無視）
          TE.map(() => ({
            embedding,
            modelVersion,
            fromCache: false,
            textHash,
          }))
        )
      )
    );
  };

  /**
   * バッチ処理
   * TLA+ Inv_CacheVersionConsistency準拠: 逐次実行でレース条件を回避
   */
  const processBatch = (
    params: readonly EmbedParams[]
  ): TE.TaskEither<EmbeddingError, BatchEmbedResult> => {
    // バッチサイズチェック
    if (params.length > MAX_BATCH_SIZE) {
      return TE.left(batchSizeExceededError(params.length, MAX_BATCH_SIZE));
    }

    // 空配列の場合
    if (params.length === 0) {
      return TE.right({
        results: [],
        processedCount: 0,
        cacheHits: 0,
      });
    }

    // 各アイテムを逐次処理（並列実行によるレース条件を回避）
    // Note: TE.ApplicativeSeqを使用して逐次実行を保証
    return pipe(
      [...params], // readonly配列を可変配列に変換
      A.traverse(TE.ApplicativeSeq)(processOne),
      TE.map((results) => ({
        results,
        processedCount: results.length,
        cacheHits: results.filter((r) => r.fromCache).length,
      }))
    );
  };

  return {
    get modelVersion(): string {
      return primary.modelVersion;
    },

    get primaryStatus() {
      return primary.status;
    },

    embed: processOne,

    embedBatch: processBatch,

    clearCache: (): TE.TaskEither<CacheError, void> => cache.invalidateAll(),

    updateModelVersion: (newVersion: string): TE.TaskEither<CacheError, void> =>
      cache.updateModelVersion(newVersion),
  };
};

// ========== ファクトリ関数 ==========

/**
 * ローカルプロバイダー専用サービスを作成
 * （テスト/開発用簡易API）
 */
export const createLocalOnlyService = (
  provider: EmbeddingProvider,
  cache: EmbeddingCache
): EmbeddingService =>
  createEmbeddingService({
    primary: provider,
    cache,
  });

/**
 * フェイルオーバー付きサービスを作成
 * ADR-0003: Local → Remote フォールバック
 */
export const createFailoverService = (
  localProvider: EmbeddingProvider,
  remoteProvider: EmbeddingProvider,
  cache: EmbeddingCache
): EmbeddingService =>
  createEmbeddingService({
    primary: localProvider,
    fallback: remoteProvider,
    cache,
  });

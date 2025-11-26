/**
 * @pce/embeddings インメモリキャッシュ
 * TLA+ Inv_CacheVersionConsistency準拠
 *
 * 設計決定（ADR-0003形式検証済み）:
 * - キャッシュキー: textHash + modelVersion（バージョン込みキー）
 * - モデルバージョン更新時: 全エントリ無効化
 * - TTL: 24時間（設定可能）
 */

import * as TE from "fp-ts/TaskEither";
import type { EmbeddingCache, CacheEntry } from "./types.js";
import { CACHE_TTL_MS } from "./types.js";
import type { CacheError } from "./errors.js";
import { cacheReadError, cacheWriteError } from "./errors.js";

/**
 * キャッシュ設定
 */
export interface CacheConfig {
  /** 初期モデルバージョン */
  readonly initialModelVersion: string;
  /** TTL（ミリ秒）。デフォルト: 24時間 */
  readonly ttlMs?: number;
  /** 最大エントリ数。デフォルト: 10000 */
  readonly maxEntries?: number;
}

/**
 * 内部エントリマップへのアクセスを持つ拡張キャッシュ型
 * getCacheStats用
 */
export interface InMemoryCacheWithInternals extends EmbeddingCache {
  _getEntries: () => Map<string, CacheEntry>;
}

/**
 * インメモリキャッシュを作成
 *
 * TLA+ Inv_CacheVersionConsistency:
 * \A t \in Text: cache[t] # <<>> => cache[t].modelVersion = currentModelVersion
 *
 * これをキャッシュキーにバージョンを含めることで実現:
 * - キー形式: `${textHash}:${modelVersion}`
 * - バージョン変更時は全エントリがキーマッチしなくなる
 *
 * @param config キャッシュ設定
 * @returns InMemoryCacheWithInternals（EmbeddingCache + 内部アクセサ）
 */
export const createInMemoryCache = (config: CacheConfig): InMemoryCacheWithInternals => {
  let currentModelVersion = config.initialModelVersion;
  const ttlMs = config.ttlMs ?? CACHE_TTL_MS;
  const maxEntries = config.maxEntries ?? 10000;
  const entries = new Map<string, CacheEntry>();

  /**
   * バージョン込みキーを生成
   * TLA+ Inv_CacheVersionConsistency を型レベルで強制
   */
  const makeKey = (textHash: string, version: string): string =>
    `${textHash}:${version}`;

  /**
   * TTL期限切れチェック
   */
  const isExpired = (entry: CacheEntry): boolean =>
    Date.now() - entry.createdAt > ttlMs;

  /**
   * LRU風の古いエントリ削除（maxEntries超過時）
   */
  const evictOldEntries = (): void => {
    if (entries.size <= maxEntries) return;

    // createdAt順でソートして古いものを削除
    const sorted = [...entries.entries()].sort(
      ([, a], [, b]) => a.createdAt - b.createdAt
    );
    const toDelete = sorted.slice(0, entries.size - maxEntries);
    toDelete.forEach(([key]) => entries.delete(key));
  };

  return {
    get currentModelVersion() {
      return currentModelVersion;
    },

    get: (textHash: string): TE.TaskEither<CacheError, CacheEntry | undefined> =>
      TE.tryCatch(
        async () => {
          const key = makeKey(textHash, currentModelVersion);
          const entry = entries.get(key);

          if (!entry) {
            return undefined;
          }

          // TTL期限切れチェック
          if (isExpired(entry)) {
            entries.delete(key);
            return undefined;
          }

          // ディープコピーを返却（呼び出し側によるミューテーション防止）
          // セキュリティ: キャッシュ汚染を防ぎ、リクエスト間での改ざん伝播を阻止
          return {
            ...entry,
            embedding: [...entry.embedding],
          };
        },
        (e) => cacheReadError(e)
      ),

    set: (
      textHash: string,
      embedding: readonly number[],
      modelVersion: string
    ): TE.TaskEither<CacheError, void> =>
      TE.tryCatch(
        async () => {
          // 呼び出し側から渡されたバージョンでキーを生成
          // フェイルオーバー時は fallback.modelVersion が渡される
          const key = makeKey(textHash, modelVersion);

          // 新しいエントリを作成（明示的に渡されたバージョンを使用）
          const entry: CacheEntry = {
            embedding: [...embedding], // イミュータブルコピー
            modelVersion,
            createdAt: Date.now(),
          };

          entries.set(key, entry);

          // 最大エントリ数を超えた場合は古いものを削除
          evictOldEntries();
        },
        (e) => cacheWriteError(e)
      ),

    invalidateAll: (): TE.TaskEither<CacheError, void> =>
      TE.tryCatch(
        async () => {
          entries.clear();
        },
        (e) => cacheWriteError(e)
      ),

    updateModelVersion: (newVersion: string): TE.TaskEither<CacheError, void> =>
      TE.tryCatch(
        async () => {
          if (newVersion !== currentModelVersion) {
            // TLA+ UpdateModelVersion: バージョン変更時は全キャッシュ無効化
            // キーにバージョンが含まれるため、実際には古いエントリは
            // 自然にマッチしなくなるが、メモリ解放のためclear
            entries.clear();
            currentModelVersion = newVersion;
          }
        },
        (e) => cacheWriteError(e)
      ),

    invalidateByModelVersion: (version: string): TE.TaskEither<CacheError, void> =>
      TE.tryCatch(
        async () => {
          // 指定バージョンを含むキーを検索して削除
          const keysToDelete: string[] = [];
          for (const key of entries.keys()) {
            if (key.endsWith(`:${version}`)) {
              keysToDelete.push(key);
            }
          }
          keysToDelete.forEach((key) => entries.delete(key));
        },
        (e) => cacheWriteError(e)
      ),

    // 内部状態へのアクセス用（getCacheStats用）
    _getEntries: () => entries,
  };
};

/**
 * キャッシュ統計情報
 */
export interface CacheStats {
  /** 現在のエントリ数 */
  readonly entryCount: number;
  /** 現在のモデルバージョン */
  readonly modelVersion: string;
  /** 最古エントリの作成時刻 */
  readonly oldestEntryAt?: number;
  /** 最新エントリの作成時刻 */
  readonly newestEntryAt?: number;
}

/**
 * createInMemoryCacheの戻り値かどうかをチェック
 */
const hasInternals = (cache: EmbeddingCache): cache is InMemoryCacheWithInternals =>
  "_getEntries" in cache && typeof (cache as InMemoryCacheWithInternals)._getEntries === "function";

/**
 * キャッシュ統計情報を取得するヘルパー
 * （デバッグ/監視用）
 * Note: createInMemoryCache の戻り値に対してのみ完全な情報を返す
 */
export const getCacheStats = (cache: EmbeddingCache): CacheStats => {
  if (!hasInternals(cache)) {
    // インターフェースのみの場合は基本情報のみ
    return {
      entryCount: 0,
      modelVersion: cache.currentModelVersion,
    };
  }

  const entries = cache._getEntries();
  const entryArray = [...entries.values()];

  if (entryArray.length === 0) {
    return {
      entryCount: 0,
      modelVersion: cache.currentModelVersion,
    };
  }

  const timestamps = entryArray.map((e) => e.createdAt);
  return {
    entryCount: entries.size,
    modelVersion: cache.currentModelVersion,
    oldestEntryAt: Math.min(...timestamps),
    newestEntryAt: Math.max(...timestamps),
  };
};

/**
 * テスト用: キャッシュをリセット
 * (テストでのみ使用)
 */
export const createTestCache = (modelVersion = "test-v1"): EmbeddingCache =>
  createInMemoryCache({ initialModelVersion: modelVersion, ttlMs: 60000 });

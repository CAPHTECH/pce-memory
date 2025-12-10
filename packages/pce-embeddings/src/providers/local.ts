/**
 * @pce/embeddings ローカル埋め込みプロバイダー
 * ADR-0003: LocalEmbeddingProvider (ONNX Runtime)
 *
 * モデル: all-MiniLM-L6-v2 (384次元, 22MB, 日本語対応)
 * 実装: @huggingface/transformers v3 (ONNX Runtime + Tokenizer統合)
 */

import * as TE from 'fp-ts/TaskEither';
import { pipe } from 'fp-ts/function';
import type { EmbeddingProvider, ProviderStatus } from '../types.js';
import { MAX_BATCH_SIZE, DEFAULT_DIMENSIONS } from '../types.js';
import type { EmbeddingError } from '../errors.js';
import { localInferenceError, batchSizeExceededError, noProviderError } from '../errors.js';

// ========== 定数 ==========

/** デフォルトモデル */
export const DEFAULT_MODEL = 'Xenova/all-MiniLM-L6-v2';

/** モデルバージョン */
export const MODEL_VERSION = 'all-MiniLM-L6-v2';

// ========== 型定義 ==========

/**
 * ローカルプロバイダー設定
 */
export interface LocalProviderConfig {
  /** モデルID（Hugging Face形式）。デフォルト: Xenova/all-MiniLM-L6-v2 */
  readonly modelId?: string;
  /** カスタムモデルバージョン */
  readonly modelVersion?: string;
  /** キャッシュディレクトリ */
  readonly cacheDir?: string;
}

// ========== モジュール状態 ==========

/** @huggingface/transformers の pipeline */
// eslint-disable-next-line @typescript-eslint/no-explicit-any
let pipeline: any = null;
/** 現在のプロバイダー状態 */
let providerStatus: ProviderStatus = 'unavailable';
/** 現在のモデルバージョン */
let currentModelVersion: string = MODEL_VERSION;
/** 初期化中のPromise（レース条件防止用） */
let initPromise: Promise<void> | null = null;

// ========== 初期化 ==========

/**
 * ローカルプロバイダーを初期化
 *
 * @huggingface/transformers v3 を使用してモデルをロード
 * 初回実行時にモデルがダウンロードされる（約22MB）
 *
 * レース条件防止:
 * - 初期化中に再度呼び出された場合、既存の初期化Promiseを返す
 * - これにより並行initLocalProvider呼び出しによる状態破壊を防止
 *
 * @param config プロバイダー設定
 */
export const initLocalProvider = async (config: LocalProviderConfig = {}): Promise<void> => {
  // 既に初期化済みの場合は即座に返す
  if (pipeline !== null) {
    return;
  }

  // 初期化中の場合は既存のPromiseを返す（重複初期化防止）
  if (initPromise !== null) {
    return initPromise;
  }

  const modelId = config.modelId ?? DEFAULT_MODEL;
  currentModelVersion = config.modelVersion ?? MODEL_VERSION;

  // 初期化Promiseを設定（後続呼び出しが待機できるように）
  initPromise = (async () => {
    try {
      // 動的インポート（ESMモジュール対応）
      const { pipeline: createPipeline, env } = await import('@huggingface/transformers');

      // キャッシュディレクトリ設定（v3でも env.cacheDir は有効）
      if (config.cacheDir) {
        env.cacheDir = config.cacheDir;
      }

      // feature-extraction パイプラインを作成
      // v3 Breaking Change: quantized: boolean → dtype: string
      // 有効な dtype 値: 'fp32'(デフォルト), 'fp16', 'q8'(8bit量子化), 'q4'(4bit量子化)
      pipeline = await createPipeline('feature-extraction', modelId, {
        dtype: 'q8', // 8bit量子化（モデルサイズ削減、推論高速化）
      });

      providerStatus = 'available';
    } catch (e) {
      // 初期化失敗時はPromiseをクリア（再試行可能に）
      initPromise = null;
      providerStatus = 'unavailable';
      throw new Error(`Failed to initialize local provider: ${e}`);
    }
  })();

  return initPromise;
};

/**
 * プロバイダーが初期化済みかチェック
 */
export const isInitialized = (): boolean => pipeline !== null;

/**
 * プロバイダーをリセット（テスト用）
 */
export const resetLocalProvider = (): void => {
  pipeline = null;
  providerStatus = 'unavailable';
  currentModelVersion = MODEL_VERSION;
  initPromise = null;
};

// ========== 埋め込み生成 ==========

/**
 * 単一テキストの埋め込みを生成
 */
const embedSingle = async (text: string): Promise<readonly number[]> => {
  if (!pipeline) {
    throw new Error('Provider not initialized');
  }

  // @huggingface/transformers の pipeline を呼び出し
  const output = await pipeline(text, {
    pooling: 'mean', // Mean pooling
    normalize: true, // L2正規化
  });

  // Tensor から配列に変換
  const embedding = Array.from(output.data as Float32Array);

  // 次元数検証
  if (embedding.length !== DEFAULT_DIMENSIONS) {
    throw new Error(
      `Unexpected embedding dimensions: ${embedding.length}, expected ${DEFAULT_DIMENSIONS}`
    );
  }

  return embedding;
};

/**
 * バッチ埋め込みを生成
 */
const embedBatchInternal = async (
  texts: readonly string[]
): Promise<readonly (readonly number[])[]> => {
  if (!pipeline) {
    throw new Error('Provider not initialized');
  }

  // 並列処理で各テキストを埋め込み
  const results = await Promise.all(texts.map((text) => embedSingle(text)));

  return results;
};

// ========== EmbeddingProvider 実装 ==========

/**
 * ローカル埋め込みプロバイダー
 *
 * TLA+ ProviderRec に対応:
 * - status: ProviderStatus
 * - modelVersion: ModelVersion
 */
export const localProvider: EmbeddingProvider = {
  get modelVersion(): string {
    return currentModelVersion;
  },

  get status(): ProviderStatus {
    return providerStatus;
  },

  embed: (text: string): TE.TaskEither<EmbeddingError, readonly number[]> =>
    pipe(
      TE.tryCatch(
        async () => {
          if (!isInitialized()) {
            throw new Error('Provider not initialized');
          }
          return embedSingle(text);
        },
        (e) => localInferenceError(e)
      )
    ),

  embedBatch: (
    texts: readonly string[]
  ): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]> => {
    // バッチサイズ制限チェック
    if (texts.length > MAX_BATCH_SIZE) {
      return TE.left(batchSizeExceededError(texts.length, MAX_BATCH_SIZE));
    }

    // 空の配列は即座に空の結果を返す
    if (texts.length === 0) {
      return TE.right([]);
    }

    return pipe(
      TE.tryCatch(
        async () => {
          if (!isInitialized()) {
            throw new Error('Provider not initialized');
          }
          return embedBatchInternal(texts);
        },
        (e) => localInferenceError(e)
      )
    );
  },
};

/**
 * ローカルプロバイダーを取得
 *
 * @returns 初期化済みの場合はプロバイダー、未初期化の場合はエラー
 */
export const getLocalProvider = (): TE.TaskEither<EmbeddingError, EmbeddingProvider> => {
  if (!isInitialized()) {
    return TE.left(noProviderError());
  }
  return TE.right(localProvider);
};

// ========== ヘルパー ==========

/**
 * テスト用スタブプロバイダーを作成
 * 決定的なベクトルを返す（ONNX依存なし）
 */
export const createStubProvider = (version = 'stub-v1'): EmbeddingProvider => ({
  modelVersion: version,
  status: 'available',

  embed: (text: string): TE.TaskEither<EmbeddingError, readonly number[]> =>
    TE.right(generateDeterministicVector(text)),

  embedBatch: (
    texts: readonly string[]
  ): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]> => {
    if (texts.length > MAX_BATCH_SIZE) {
      return TE.left(batchSizeExceededError(texts.length, MAX_BATCH_SIZE));
    }
    return TE.right(texts.map(generateDeterministicVector));
  },
});

/**
 * テキストから決定的なベクトルを生成
 * （テスト用：同じ入力には同じ出力）
 */
const generateDeterministicVector = (text: string): readonly number[] => {
  const hash = simpleHash(text);
  const vector: number[] = [];
  for (let i = 0; i < DEFAULT_DIMENSIONS; i++) {
    // 決定的な疑似乱数を生成（-1 〜 1 の範囲）
    vector.push(Math.sin(hash * (i + 1) * 0.001) * 0.5);
  }
  return vector;
};

/**
 * 単純なハッシュ関数
 */
const simpleHash = (text: string): number => {
  let hash = 0;
  for (let i = 0; i < text.length; i++) {
    hash = (hash << 5) - hash + text.charCodeAt(i);
    hash |= 0; // 32bit整数に変換
  }
  return hash;
};

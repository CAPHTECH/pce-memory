/**
 * @pce/embeddings エラー型定義
 * TLA+ ErrorType + ADR-0003仕様に準拠
 * パターン: apps/pce-memory/src/domain/errors.ts
 */

// ========== TLA+ ErrorType ==========

/**
 * TLA+: ErrorType == {"PROVIDER_UNAVAILABLE", "TIMEOUT", "UNKNOWN", "STALE_MODEL_VERSION"}
 * + ADR-0003追加エラーコード
 */
export type EmbeddingErrorCode =
  // TLA+ 定義
  | "PROVIDER_UNAVAILABLE"    // 両プロバイダーが利用不可
  | "TIMEOUT"                 // タイムアウト
  | "STALE_MODEL_VERSION"     // CompleteProcessingStale: バージョン不一致
  // ADR-0003 追加
  | "BATCH_SIZE_EXCEEDED"     // バッチサイズ超過（MAX=32）
  | "REDACT_REQUIRED"         // Confidentialデータのredact失敗
  | "LOCAL_INFERENCE_FAILED"  // ローカルONNX推論失敗
  | "REMOTE_API_FAILED"       // リモートAPI呼び出し失敗
  | "TOKENIZATION_FAILED"     // トークナイズ失敗
  | "INVALID_INPUT"           // 不正な入力
  | "NO_PROVIDER"             // プロバイダー未登録
  | "CACHE_ERROR";            // キャッシュ操作失敗

/**
 * 埋め込みエラー型
 * TLA+: FailedRec == [text: Text, requestId: RequestId, error: ErrorType]
 */
export interface EmbeddingError {
  readonly _tag: "EmbeddingError";
  readonly code: EmbeddingErrorCode;
  readonly message: string;
  readonly cause?: unknown;
  /** 失敗したプロバイダー（デバッグ用） */
  readonly provider?: "primary" | "fallback";
}

/**
 * エラー生成関数
 */
export const embeddingError = (
  code: EmbeddingErrorCode,
  message: string,
  cause?: unknown,
  provider?: "primary" | "fallback"
): EmbeddingError => {
  const result: EmbeddingError = {
    _tag: "EmbeddingError",
    code,
    message,
  };
  if (cause !== undefined) {
    (result as { cause: unknown }).cause = cause;
  }
  if (provider !== undefined) {
    (result as { provider: "primary" | "fallback" }).provider = provider;
  }
  return result;
};

// ========== ショートカット関数 ==========

/** TLA+: PROVIDER_UNAVAILABLE */
export const providerUnavailableError = (
  message = "No available embedding provider"
): EmbeddingError => embeddingError("PROVIDER_UNAVAILABLE", message);

/** TLA+: STALE_MODEL_VERSION */
export const staleModelVersionError = (
  expected: string,
  actual: string
): EmbeddingError =>
  embeddingError(
    "STALE_MODEL_VERSION",
    `Model version mismatch: expected ${expected}, got ${actual}`
  );

/** ADR-0003: BATCH_SIZE_EXCEEDED */
export const batchSizeExceededError = (
  actual: number,
  max: number
): EmbeddingError =>
  embeddingError(
    "BATCH_SIZE_EXCEEDED",
    `Batch size ${actual} exceeds maximum ${max}`
  );

/** Alloy RedactBeforeEmbed違反 */
export const redactRequiredError = (
  message = "Confidential data must be redacted before embedding"
): EmbeddingError => embeddingError("REDACT_REQUIRED", message);

/** ローカル推論失敗 */
export const localInferenceError = (cause: unknown): EmbeddingError =>
  embeddingError(
    "LOCAL_INFERENCE_FAILED",
    "Local ONNX inference failed",
    cause,
    "primary"
  );

/** リモートAPI失敗 */
export const remoteApiError = (
  message: string,
  cause?: unknown
): EmbeddingError =>
  embeddingError("REMOTE_API_FAILED", message, cause, "fallback");

/** トークナイズ失敗 */
export const tokenizationError = (cause: unknown): EmbeddingError =>
  embeddingError("TOKENIZATION_FAILED", "Tokenization failed", cause);

/** 不正入力 */
export const invalidInputError = (message: string): EmbeddingError =>
  embeddingError("INVALID_INPUT", message);

/** プロバイダー未登録 */
export const noProviderError = (): EmbeddingError =>
  embeddingError("NO_PROVIDER", "No embedding provider registered");

/** キャッシュ操作失敗（CacheErrorをEmbeddingErrorに変換） */
export const cacheOperationError = (
  message: string,
  cause?: unknown
): EmbeddingError => embeddingError("CACHE_ERROR", message, cause);

// ========== CacheError ==========

/**
 * キャッシュエラーコード
 */
export type CacheErrorCode =
  | "CACHE_READ_ERROR"
  | "CACHE_WRITE_ERROR"
  | "VERSION_MISMATCH";

/**
 * キャッシュエラー型
 */
export interface CacheError {
  readonly _tag: "CacheError";
  readonly code: CacheErrorCode;
  readonly message: string;
  readonly cause?: unknown;
}

/**
 * キャッシュエラー生成関数
 */
export const cacheError = (
  code: CacheErrorCode,
  message: string,
  cause?: unknown
): CacheError => ({
  _tag: "CacheError",
  code,
  message,
  cause,
});

// ========== キャッシュエラーショートカット ==========

export const cacheReadError = (cause?: unknown): CacheError =>
  cacheError("CACHE_READ_ERROR", "Cache read failed", cause);

export const cacheWriteError = (cause?: unknown): CacheError =>
  cacheError("CACHE_WRITE_ERROR", "Cache write failed", cause);

export const versionMismatchError = (
  expected: string,
  actual: string
): CacheError =>
  cacheError(
    "VERSION_MISMATCH",
    `Cache version mismatch: expected ${expected}, got ${actual}`
  );

// ========== 型ガード ==========

/**
 * EmbeddingErrorかどうかを判定
 */
export const isEmbeddingError = (e: unknown): e is EmbeddingError =>
  typeof e === "object" &&
  e !== null &&
  "_tag" in e &&
  (e as EmbeddingError)._tag === "EmbeddingError";

/**
 * CacheErrorかどうかを判定
 */
export const isCacheError = (e: unknown): e is CacheError =>
  typeof e === "object" &&
  e !== null &&
  "_tag" in e &&
  (e as CacheError)._tag === "CacheError";

/**
 * @pce/embeddings - Embedding provider abstraction for PCE
 *
 * ADR-0003で形式検証された設計:
 * - キャッシュキー: バージョン込み（textHash + modelVersion）
 * - フェイルオーバー: 即時フェイルオーバー
 * - Redact順序: Redact-before-Embed
 *
 * @see docs/adr/0003-embedding-system-design.md
 * @see docs/spec/tlaplus/pce_embedding.tla
 * @see docs/spec/alloy/embedding.als
 */

// ========== 型定義 ==========
export type {
  // TLA+ Constants
  ProviderStatus,
  SensitivityLevel,
  // Cache
  CacheEntry,
  // Provider
  EmbeddingProvider,
  // Cache Interface
  EmbeddingCache,
  // Service Types
  EmbedParams,
  EmbedResult,
  BatchEmbedResult,
  // Config (Note: LocalProviderConfig is exported from providers/local.js)
  RemoteProviderConfig,
  EmbeddingServiceConfig,
} from './types.js';

export { MAX_BATCH_SIZE, CACHE_TTL_MS, DEFAULT_DIMENSIONS } from './types.js';

// ========== エラー型 ==========
export type { EmbeddingErrorCode, EmbeddingError, CacheErrorCode, CacheError } from './errors.js';

export {
  // 生成関数
  embeddingError,
  cacheError,
  // ショートカット - EmbeddingError
  providerUnavailableError,
  staleModelVersionError,
  batchSizeExceededError,
  redactRequiredError,
  localInferenceError,
  remoteApiError,
  tokenizationError,
  invalidInputError,
  noProviderError,
  cacheOperationError,
  // ショートカット - CacheError
  cacheReadError,
  cacheWriteError,
  versionMismatchError,
  // 型ガード
  isEmbeddingError,
  isCacheError,
} from './errors.js';

// ========== Hash ==========
export { computeContentHash, normalizeText, isValidHash } from './hash.js';

// ========== Redact ==========
export type { PreparedText, RedactError } from './redact.js';
export { prepareForEmbedding, requiresRedact, redactError, isRedactError } from './redact.js';

// ========== Cache ==========
export type { CacheConfig, CacheStats, InMemoryCacheWithInternals } from './cache.js';
export { createInMemoryCache, getCacheStats, createTestCache } from './cache.js';

// ========== Local Provider ==========
export type { LocalProviderConfig } from './providers/local.js';
export {
  DEFAULT_MODEL,
  MODEL_VERSION,
  initLocalProvider,
  isInitialized,
  resetLocalProvider,
  disposeLocalProvider,
  localProvider,
  getLocalProvider,
  createStubProvider,
} from './providers/local.js';

// ========== Remote Provider ==========
export type { RemoteProviderOptions } from './providers/remote.js';
export {
  createRemoteProvider,
  createOpenAIProvider,
  createAzureOpenAIProvider,
  createUnavailableProvider,
} from './providers/remote.js';

// ========== Service ==========
export type { EmbeddingService, ServiceError } from './service.js';
export {
  createEmbeddingService,
  createLocalOnlyService,
  createFailoverService,
} from './service.js';

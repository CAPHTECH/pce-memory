/**
 * pce-embeddings/errors.ts のテスト
 * エラーファクトリ関数とtype guardのカバレッジ
 */
import { describe, it, expect } from 'vitest';
import {
  embeddingError,
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
  cacheError,
  cacheReadError,
  cacheWriteError,
  versionMismatchError,
  isEmbeddingError,
  isCacheError,
} from '../src/errors';

describe('embeddingError', () => {
  it('creates error with code and message', () => {
    const err = embeddingError('TIMEOUT', 'request timed out');
    expect(err._tag).toBe('EmbeddingError');
    expect(err.code).toBe('TIMEOUT');
    expect(err.message).toBe('request timed out');
    expect(err.cause).toBeUndefined();
    expect(err.provider).toBeUndefined();
  });

  it('includes cause when provided', () => {
    const cause = new Error('original');
    const err = embeddingError('TIMEOUT', 'timeout', cause);
    expect(err.cause).toBe(cause);
  });

  it('includes provider when provided', () => {
    const err = embeddingError('REMOTE_API_FAILED', 'api down', undefined, 'fallback');
    expect(err.provider).toBe('fallback');
  });
});

describe('embedding error shortcuts', () => {
  it('providerUnavailableError', () => {
    const err = providerUnavailableError();
    expect(err.code).toBe('PROVIDER_UNAVAILABLE');
    expect(err.message).toBe('No available embedding provider');
  });

  it('providerUnavailableError with custom message', () => {
    const err = providerUnavailableError('custom');
    expect(err.message).toBe('custom');
  });

  it('staleModelVersionError', () => {
    const err = staleModelVersionError('v1', 'v2');
    expect(err.code).toBe('STALE_MODEL_VERSION');
    expect(err.message).toContain('v1');
    expect(err.message).toContain('v2');
  });

  it('batchSizeExceededError', () => {
    const err = batchSizeExceededError(50, 32);
    expect(err.code).toBe('BATCH_SIZE_EXCEEDED');
    expect(err.message).toContain('50');
    expect(err.message).toContain('32');
  });

  it('redactRequiredError', () => {
    const err = redactRequiredError();
    expect(err.code).toBe('REDACT_REQUIRED');
  });

  it('localInferenceError', () => {
    const cause = new Error('onnx failed');
    const err = localInferenceError(cause);
    expect(err.code).toBe('LOCAL_INFERENCE_FAILED');
    expect(err.provider).toBe('primary');
    expect(err.cause).toBe(cause);
  });

  it('remoteApiError', () => {
    const err = remoteApiError('500 error', new Error('http'));
    expect(err.code).toBe('REMOTE_API_FAILED');
    expect(err.provider).toBe('fallback');
  });

  it('tokenizationError', () => {
    const err = tokenizationError(new Error('bad token'));
    expect(err.code).toBe('TOKENIZATION_FAILED');
    expect(err.cause).toBeInstanceOf(Error);
  });

  it('invalidInputError', () => {
    const err = invalidInputError('empty text');
    expect(err.code).toBe('INVALID_INPUT');
    expect(err.message).toBe('empty text');
  });

  it('noProviderError', () => {
    const err = noProviderError();
    expect(err.code).toBe('NO_PROVIDER');
  });

  it('cacheOperationError', () => {
    const err = cacheOperationError('cache failed', new Error('disk'));
    expect(err.code).toBe('CACHE_ERROR');
    expect(err.cause).toBeInstanceOf(Error);
  });
});

describe('cacheError', () => {
  it('creates cache error with code and message', () => {
    const err = cacheError('CACHE_READ_ERROR', 'read failed');
    expect(err._tag).toBe('CacheError');
    expect(err.code).toBe('CACHE_READ_ERROR');
  });

  it('cacheReadError', () => {
    const err = cacheReadError(new Error('io'));
    expect(err.code).toBe('CACHE_READ_ERROR');
    expect(err.cause).toBeInstanceOf(Error);
  });

  it('cacheWriteError', () => {
    const err = cacheWriteError();
    expect(err.code).toBe('CACHE_WRITE_ERROR');
  });

  it('versionMismatchError', () => {
    const err = versionMismatchError('v1', 'v2');
    expect(err.code).toBe('VERSION_MISMATCH');
    expect(err.message).toContain('v1');
  });
});

describe('type guards', () => {
  it('isEmbeddingError returns true for EmbeddingError', () => {
    const err = embeddingError('TIMEOUT', 'test');
    expect(isEmbeddingError(err)).toBe(true);
  });

  it('isEmbeddingError returns false for non-errors', () => {
    expect(isEmbeddingError(null)).toBe(false);
    expect(isEmbeddingError(undefined)).toBe(false);
    expect(isEmbeddingError('string')).toBe(false);
    expect(isEmbeddingError({ _tag: 'Other' })).toBe(false);
  });

  it('isCacheError returns true for CacheError', () => {
    const err = cacheReadError();
    expect(isCacheError(err)).toBe(true);
  });

  it('isCacheError returns false for non-errors', () => {
    expect(isCacheError(null)).toBe(false);
    expect(isCacheError({ _tag: 'EmbeddingError' })).toBe(false);
  });
});

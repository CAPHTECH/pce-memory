/**
 * domain/errors.ts のテスト
 * エラー生成ファクトリ関数の未カバー部分
 */
import { describe, it, expect } from 'vitest';
import {
  domainError,
  validationError,
  rateLimitError,
  claimNotFoundError,
  dbError,
  layerSelfDependencyError,
  layerCycleError,
  scopeNotActiveError,
  syncPushError,
  syncPullError,
  syncValidationError,
  syncPathError,
  syncStatusError,
} from '../src/domain/errors';

describe('domainError', () => {
  it('creates error with _tag, code, and message', () => {
    const err = domainError('VALIDATION_ERROR', 'bad input');
    expect(err._tag).toBe('DomainError');
    expect(err.code).toBe('VALIDATION_ERROR');
    expect(err.message).toBe('bad input');
    expect(err.cause).toBeUndefined();
  });

  it('creates error with cause', () => {
    const cause = new Error('original');
    const err = domainError('DB_ERROR', 'db failed', cause);
    expect(err.cause).toBe(cause);
  });
});

describe('error shortcut factories', () => {
  it('validationError creates VALIDATION_ERROR', () => {
    const err = validationError('field invalid');
    expect(err.code).toBe('VALIDATION_ERROR');
    expect(err.message).toBe('field invalid');
  });

  it('rateLimitError creates RATE_LIMIT', () => {
    const err = rateLimitError();
    expect(err.code).toBe('RATE_LIMIT');
    expect(err.message).toBe('rate limit exceeded');
  });

  it('claimNotFoundError includes claim id', () => {
    const err = claimNotFoundError('clm_abc');
    expect(err.code).toBe('CLAIM_NOT_FOUND');
    expect(err.message).toBe('claim not found: clm_abc');
  });

  it('dbError wraps cause', () => {
    const cause = new Error('connection timeout');
    const err = dbError(cause);
    expect(err.code).toBe('DB_ERROR');
    expect(err.message).toBe('database operation failed');
    expect(err.cause).toBe(cause);
  });

  it('layerSelfDependencyError includes layer name', () => {
    const err = layerSelfDependencyError('session');
    expect(err.code).toBe('LAYER_SELF_DEPENDENCY');
    expect(err.message).toBe('layer "session" cannot depend on itself');
  });

  it('layerCycleError includes from and to', () => {
    const err = layerCycleError('A', 'B');
    expect(err.code).toBe('LAYER_CYCLE_DETECTED');
    expect(err.message).toBe('cycle detected: A -> B');
  });

  it('scopeNotActiveError includes scope id', () => {
    const err = scopeNotActiveError('sc_123');
    expect(err.code).toBe('SCOPE_NOT_ACTIVE');
    expect(err.message).toBe('scope not active: sc_123');
  });
});

describe('sync error factories', () => {
  it('syncPushError creates SYNC_PUSH_FAILED', () => {
    const err = syncPushError('write failed', new Error('disk full'));
    expect(err.code).toBe('SYNC_PUSH_FAILED');
    expect(err.message).toBe('write failed');
    expect(err.cause).toBeInstanceOf(Error);
  });

  it('syncPullError creates SYNC_PULL_FAILED', () => {
    const err = syncPullError('read failed');
    expect(err.code).toBe('SYNC_PULL_FAILED');
    expect(err.message).toBe('read failed');
  });

  it('syncValidationError creates SYNC_VALIDATION_ERROR', () => {
    const err = syncValidationError('invalid json', { detail: 'parse error' });
    expect(err.code).toBe('SYNC_VALIDATION_ERROR');
    expect(err.message).toBe('invalid json');
    expect(err.cause).toEqual({ detail: 'parse error' });
  });

  it('syncPathError creates SYNC_PATH_ERROR', () => {
    const err = syncPathError('path traversal detected');
    expect(err.code).toBe('SYNC_PATH_ERROR');
    expect(err.message).toBe('path traversal detected');
  });

  it('syncStatusError creates SYNC_STATUS_FAILED', () => {
    const err = syncStatusError('git not found', new Error('ENOENT'));
    expect(err.code).toBe('SYNC_STATUS_FAILED');
    expect(err.message).toBe('git not found');
  });
});

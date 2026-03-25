/**
 * config/env.ts のテスト
 * 環境変数読み込みとトークン検証のカバレッジ
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { loadEnv, validateToken, clearEnvCache } from '../src/config/env';

// 元の環境変数を退避
const originalEnv = { ...process.env };

beforeEach(() => {
  clearEnvCache();
});

afterEach(() => {
  // 環境変数を復元
  process.env = { ...originalEnv };
  clearEnvCache();
});

describe('loadEnv', () => {
  it('returns default values', () => {
    delete process.env.PCE_DB;
    delete process.env.NODE_ENV;
    const env = loadEnv();
    expect(env.PCE_DB).toBe(':memory:');
    expect(env.NODE_ENV).toBe('development');
  });

  it('reads PCE_DB from env', () => {
    process.env.PCE_DB = '/tmp/test.db';
    const env = loadEnv();
    expect(env.PCE_DB).toBe('/tmp/test.db');
  });

  it('reads optional PCE_TOKEN', () => {
    process.env.PCE_TOKEN = 'test-token';
    const env = loadEnv();
    expect(env.PCE_TOKEN).toBe('test-token');
  });

  it('caches result across calls', () => {
    const env1 = loadEnv();
    const env2 = loadEnv();
    expect(env1).toBe(env2); // same reference
  });

  it('throws for production without PCE_TOKEN', () => {
    process.env.NODE_ENV = 'production';
    delete process.env.PCE_TOKEN;
    expect(() => loadEnv()).toThrow('PCE_TOKEN is required in production');
  });

  it('allows production with PCE_TOKEN', () => {
    process.env.NODE_ENV = 'production';
    process.env.PCE_TOKEN = 'secure-token';
    const env = loadEnv();
    expect(env.NODE_ENV).toBe('production');
    expect(env.PCE_TOKEN).toBe('secure-token');
  });

  it('reads optional AUDIT_LOG_PATH', () => {
    process.env.AUDIT_LOG_PATH = '/tmp/audit.log';
    const env = loadEnv();
    expect(env.AUDIT_LOG_PATH).toBe('/tmp/audit.log');
  });

  it('reads optional PCE_POLICY', () => {
    process.env.PCE_POLICY = '/tmp/policy.yaml';
    const env = loadEnv();
    expect(env.PCE_POLICY).toBe('/tmp/policy.yaml');
  });
});

describe('validateToken', () => {
  it('allows any request in dev without PCE_TOKEN', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'development' as const };
    expect(validateToken(undefined, env)).toBe(true);
  });

  it('allows any request in test without PCE_TOKEN', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'test' as const };
    expect(validateToken(undefined, env)).toBe(true);
  });

  it('rejects missing token when PCE_TOKEN is set', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'development' as const, PCE_TOKEN: 'secret' };
    expect(validateToken(undefined, env)).toBe(false);
  });

  it('accepts matching token', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'production' as const, PCE_TOKEN: 'my-token' };
    expect(validateToken('my-token', env)).toBe(true);
  });

  it('rejects wrong token', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'production' as const, PCE_TOKEN: 'correct' };
    expect(validateToken('wrong', env)).toBe(false);
  });

  it('rejects token with different length (timing-safe)', () => {
    const env = {
      PCE_DB: ':memory:',
      NODE_ENV: 'production' as const,
      PCE_TOKEN: 'long-secret-token',
    };
    expect(validateToken('short', env)).toBe(false);
  });

  it('rejects when production has no token at all', () => {
    const env = { PCE_DB: ':memory:', NODE_ENV: 'production' as const };
    expect(validateToken(undefined, env)).toBe(false);
  });
});

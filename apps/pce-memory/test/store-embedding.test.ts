/**
 * store/embedding.ts のテスト
 * DuckDB永続化キャッシュ: 構造検証 + get miss パスのカバレッジ
 */
import { describe, it, expect, beforeEach } from 'vitest';
import * as E from 'fp-ts/Either';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { createDuckDBCache, getDuckDBCacheStats, cleanupExpiredEntries } from '../src/store/embedding';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('createDuckDBCache', () => {
  it('exposes currentModelVersion', () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    expect(cache.currentModelVersion).toBe('v1.0');
  });

  it('get returns Right(undefined) for missing key', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const result = await cache.get('nonexistent')();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it('invalidateAll succeeds on empty cache', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const result = await cache.invalidateAll()();
    expect(E.isRight(result)).toBe(true);
  });

  it('updateModelVersion changes version', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const result = await cache.updateModelVersion('v2.0')();
    expect(E.isRight(result)).toBe(true);
    expect(cache.currentModelVersion).toBe('v2.0');
  });

  it('updateModelVersion no-op for same version', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const result = await cache.updateModelVersion('v1.0')();
    expect(E.isRight(result)).toBe(true);
    expect(cache.currentModelVersion).toBe('v1.0');
  });

  it('invalidateByModelVersion succeeds on empty cache', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const result = await cache.invalidateByModelVersion('v1.0')();
    expect(E.isRight(result)).toBe(true);
  });
});

describe('getDuckDBCacheStats', () => {
  it('returns zero counts for empty cache', async () => {
    const cache = createDuckDBCache({ initialModelVersion: 'v1.0' });
    const stats = await getDuckDBCacheStats(cache);
    expect(stats.currentVersionCount).toBe(0);
    expect(stats.totalCount).toBe(0);
    expect(stats.modelVersion).toBe('v1.0');
  });
});

describe('cleanupExpiredEntries', () => {
  it('returns 0 when no entries exist', async () => {
    const count = await cleanupExpiredEntries(86400000);
    expect(count).toBe(0);
  });
});

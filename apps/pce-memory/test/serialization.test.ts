/**
 * シリアライゼーションユーティリティのテスト
 * DuckDB BigIntタイムスタンプの正規化をテスト
 */
import { describe, it, expect } from 'vitest';
import {
  normalizeTimestamp,
  normalizeRowTimestamps,
  normalizeRowsTimestamps,
  bigIntReplacer,
  safeJsonStringify,
} from '../src/utils/serialization';

describe('normalizeTimestamp', () => {
  it('BigIntをISO 8601文字列に変換する', () => {
    // DuckDBはマイクロ秒単位で返す
    // 2024-01-01 00:00:00 UTC = 1704067200000 ms = 1704067200000000 μs
    const bigintTimestamp = 1704067200000000n;
    const result = normalizeTimestamp(bigintTimestamp);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('DuckDBTimestampオブジェクト({micros: bigint})をISO 8601文字列に変換する', () => {
    // DuckDB node-api 1.4.x では {micros: bigint} オブジェクト形式で返される
    const duckdbTimestamp = { micros: 1704067200000000n };
    const result = normalizeTimestamp(duckdbTimestamp);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('DateオブジェクトをISO 8601文字列に変換する', () => {
    const date = new Date('2024-01-01T00:00:00.000Z');
    const result = normalizeTimestamp(date);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('文字列はそのまま返す', () => {
    const str = '2024-01-01T00:00:00.000Z';
    const result = normalizeTimestamp(str);
    expect(result).toBe(str);
  });

  it('数値はそのまま返す', () => {
    const num = 12345;
    const result = normalizeTimestamp(num);
    expect(result).toBe(num);
  });

  it('nullはそのまま返す', () => {
    const result = normalizeTimestamp(null);
    expect(result).toBeNull();
  });

  it('undefinedはそのまま返す', () => {
    const result = normalizeTimestamp(undefined);
    expect(result).toBeUndefined();
  });
});

describe('normalizeRowTimestamps', () => {
  it('デフォルトタイムスタンプフィールドを正規化する', () => {
    const row = {
      id: 'test-id',
      text: 'test text',
      created_at: 1704067200000000n,
      updated_at: 1704067200000000n,
      recency_anchor: 1704067200000000n,
    };

    const result = normalizeRowTimestamps(row);

    expect(result.id).toBe('test-id');
    expect(result.text).toBe('test text');
    expect(result.created_at).toBe('2024-01-01T00:00:00.000Z');
    expect(result.updated_at).toBe('2024-01-01T00:00:00.000Z');
    expect(result.recency_anchor).toBe('2024-01-01T00:00:00.000Z');
  });

  it('カスタムタイムスタンプフィールドを正規化する', () => {
    const row = {
      id: 'test-id',
      custom_ts: 1704067200000000n,
    };

    const result = normalizeRowTimestamps(row, ['custom_ts']);

    expect(result.id).toBe('test-id');
    expect(result.custom_ts).toBe('2024-01-01T00:00:00.000Z');
  });

  it('存在しないフィールドは無視する', () => {
    const row = {
      id: 'test-id',
    };

    const result = normalizeRowTimestamps(row, ['created_at', 'updated_at']);

    expect(result.id).toBe('test-id');
    expect(result).not.toHaveProperty('created_at');
    expect(result).not.toHaveProperty('updated_at');
  });

  it('元のオブジェクトを変更しない', () => {
    const row = {
      id: 'test-id',
      created_at: 1704067200000000n,
    };

    normalizeRowTimestamps(row);

    // 元のオブジェクトは変更されていない
    expect(typeof row.created_at).toBe('bigint');
  });
});

describe('normalizeRowsTimestamps', () => {
  it('配列の各要素を正規化する', () => {
    const rows = [
      { id: '1', created_at: 1704067200000000n },
      { id: '2', created_at: 1704153600000000n }, // 2024-01-02
    ];

    const result = normalizeRowsTimestamps(rows);

    expect(result).toHaveLength(2);
    expect(result[0]?.created_at).toBe('2024-01-01T00:00:00.000Z');
    expect(result[1]?.created_at).toBe('2024-01-02T00:00:00.000Z');
  });

  it('空配列を処理する', () => {
    const result = normalizeRowsTimestamps([]);
    expect(result).toEqual([]);
  });
});

describe('JSON.stringify互換性', () => {
  it('正規化後のオブジェクトはJSON.stringifyできる', () => {
    const row = {
      id: 'test-id',
      text: 'test text',
      created_at: 1704067200000000n,
      updated_at: 1704067200000000n,
    };

    const normalized = normalizeRowTimestamps(row);

    // BigIntがあるとJSON.stringifyはエラーになるが、正規化後は成功する
    expect(() => JSON.stringify(normalized)).not.toThrow();

    const json = JSON.stringify(normalized);
    const parsed = JSON.parse(json);
    expect(parsed.created_at).toBe('2024-01-01T00:00:00.000Z');
  });

  it('正規化前のBigIntはJSON.stringifyでエラーになる', () => {
    const row = {
      id: 'test-id',
      created_at: 1704067200000000n,
    };

    expect(() => JSON.stringify(row)).toThrow();
  });
});

describe('bigIntReplacer', () => {
  it('タイムスタンプBigIntをISO 8601文字列に変換する', () => {
    const timestamp = 1704067200000000n; // 2024-01-01 00:00:00 UTC in microseconds
    const result = bigIntReplacer('created_at', timestamp);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('DuckDBTimestampオブジェクト({micros: bigint})をISO 8601文字列に変換する', () => {
    const duckdbTimestamp = { micros: 1704067200000000n };
    const result = bigIntReplacer('created_at', duckdbTimestamp);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('変換済みDuckDBTimestamp({micros: string})から文字列を抽出する', () => {
    // JSON.stringifyの深さ優先処理により、内部のbigintが先に変換されるケース
    const convertedTimestamp = { micros: '2024-01-01T00:00:00.000Z' };
    const result = bigIntReplacer('created_at', convertedTimestamp);
    expect(result).toBe('2024-01-01T00:00:00.000Z');
  });

  it('小さいBigIntをnumberに変換する', () => {
    const smallBigInt = 12345n;
    const result = bigIntReplacer('count', smallBigInt);
    expect(result).toBe(12345);
  });

  it('Number.MAX_SAFE_INTEGER以下のBigIntをnumberに変換する', () => {
    const safeBigInt = BigInt(Number.MAX_SAFE_INTEGER);
    const result = bigIntReplacer('value', safeBigInt);
    expect(result).toBe(Number.MAX_SAFE_INTEGER);
  });

  it('非BigInt値はそのまま返す', () => {
    expect(bigIntReplacer('key', 'string')).toBe('string');
    expect(bigIntReplacer('key', 123)).toBe(123);
    expect(bigIntReplacer('key', null)).toBeNull();
    expect(bigIntReplacer('key', { nested: 'object' })).toEqual({ nested: 'object' });
  });
});

describe('safeJsonStringify', () => {
  it('BigIntを含むオブジェクトを安全にシリアライズする', () => {
    const obj = {
      id: 'test-id',
      created_at: 1704067200000000n,
      count: 42n,
    };

    const json = safeJsonStringify(obj);
    const parsed = JSON.parse(json);

    expect(parsed.id).toBe('test-id');
    expect(parsed.created_at).toBe('2024-01-01T00:00:00.000Z');
    expect(parsed.count).toBe(42);
  });

  it('DuckDBTimestampオブジェクトを含むオブジェクトを安全にシリアライズする', () => {
    const obj = {
      id: 'test-id',
      created_at: { micros: 1704067200000000n },
      updated_at: { micros: 1704153600000000n },
    };

    const json = safeJsonStringify(obj);
    const parsed = JSON.parse(json);

    expect(parsed.id).toBe('test-id');
    expect(parsed.created_at).toBe('2024-01-01T00:00:00.000Z');
    expect(parsed.updated_at).toBe('2024-01-02T00:00:00.000Z');
  });

  it('ネストされたBigIntを安全にシリアライズする', () => {
    const obj = {
      claim: {
        id: 'claim-1',
        created_at: 1704067200000000n,
      },
      evidences: [
        { at: 1704153600000000n }, // 2024-01-02
      ],
    };

    const json = safeJsonStringify(obj);
    const parsed = JSON.parse(json);

    expect(parsed.claim.created_at).toBe('2024-01-01T00:00:00.000Z');
    expect(parsed.evidences[0].at).toBe('2024-01-02T00:00:00.000Z');
  });

  it('BigIntがないオブジェクトも正常にシリアライズする', () => {
    const obj = {
      id: 'test-id',
      name: 'test',
      count: 42,
    };

    const json = safeJsonStringify(obj);
    expect(json).toBe(JSON.stringify(obj));
  });
});

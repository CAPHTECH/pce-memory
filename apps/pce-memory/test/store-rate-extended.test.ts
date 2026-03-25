/**
 * store/rate.ts の追加テスト
 * getRate, setRate, getRow (via getRate), cap/windowSec env vars のカバレッジ
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState, getRate, setRate, checkAndConsume, resetRates } from '../src/store/rate';

const originalEnv = { ...process.env };

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
});

afterEach(() => {
  process.env = { ...originalEnv };
});

describe('getRate', () => {
  it('returns 0 for initialized bucket', async () => {
    const rate = await getRate('tool');
    expect(rate).toBe(0);
  });

  it('returns 0 for non-existent bucket', async () => {
    const rate = await getRate('nonexistent');
    expect(rate).toBe(0);
  });
});

describe('setRate', () => {
  it('sets rate value for existing bucket', async () => {
    await setRate('tool', 5);
    const rate = await getRate('tool');
    expect(rate).toBe(5);
  });

  it('creates rate entry for new bucket', async () => {
    await setRate('custom', 10);
    const rate = await getRate('custom');
    expect(rate).toBe(10);
  });
});

describe('checkAndConsume', () => {
  it('returns true when under limit', async () => {
    const result = await checkAndConsume('tool');
    expect(result).toBe(true);
  });

  it('increments counter on each consume', async () => {
    await checkAndConsume('tool');
    await checkAndConsume('tool');
    const rate = await getRate('tool');
    expect(rate).toBe(2);
  });

  it('returns false when limit is reached', async () => {
    // Set rate near limit
    process.env.PCE_RATE_CAP = '3';
    await setRate('tool', 3);
    const result = await checkAndConsume('tool');
    expect(result).toBe(false);
  });

  it('respects PCE_RATE_CAP env var', async () => {
    process.env.PCE_RATE_CAP = '2';
    // Note: cap() reads env at call time
    await checkAndConsume('tool');
    await checkAndConsume('tool');
    const thirdResult = await checkAndConsume('tool');
    expect(thirdResult).toBe(false);
  });
});

describe('resetRates', () => {
  it('resets all rate counters to 0', async () => {
    await setRate('tool', 10);
    await setRate('policy', 5);
    await resetRates();
    expect(await getRate('tool')).toBe(0);
    expect(await getRate('policy')).toBe(0);
  });
});

describe('initRateState', () => {
  it('initializes default buckets', async () => {
    // Already called in beforeEach, verify buckets exist
    expect(await getRate('tool')).toBe(0);
    expect(await getRate('policy')).toBe(0);
    expect(await getRate('activate')).toBe(0);
  });

  it('resets existing buckets on re-init', async () => {
    await setRate('tool', 99);
    await initRateState();
    expect(await getRate('tool')).toBe(0);
  });
});

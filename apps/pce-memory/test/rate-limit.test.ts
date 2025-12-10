import { describe, it, expect, beforeEach } from 'vitest';
import { checkAndConsume, initRateState, resetRates } from '../src/store/rate';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '1';
  process.env.PCE_RATE_WINDOW = '100'; // large window to avoid auto-reset
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe('rate limit', () => {
  it('blocks when cap reached', async () => {
    expect(await checkAndConsume('tool')).toBe(true);
    expect(await checkAndConsume('tool')).toBe(false);
  });

  it('resets after window elapsed', async () => {
    const conn = await getConnection();
    expect(await checkAndConsume('tool')).toBe(true);
    // simulate window expiry by setting last_reset back in time
    await conn.run("UPDATE rate_state SET last_reset = last_reset - 200 WHERE bucket = 'tool'");
    expect(await checkAndConsume('tool')).toBe(true);
  });

  // Bug fix: initRateStateがINSERT OR IGNOREを使用していたため、
  // デーモン再起動時にrate limitがリセットされなかった問題の検証テスト
  it('initRateState should reset values on daemon restart', async () => {
    const conn = await getConnection();

    // rate limitに到達
    expect(await checkAndConsume('tool')).toBe(true);
    expect(await checkAndConsume('tool')).toBe(false);

    // 現在の状態を確認（value = 1 = cap）
    let reader = await conn.runAndReadAll("SELECT value FROM rate_state WHERE bucket = 'tool'");
    let rows = reader.getRowObjects() as { value: number }[];
    expect(rows[0].value).toBe(1); // cap = 1

    // デーモン再起動をシミュレート（initRateStateを再度呼び出す）
    await initRateState();

    // initRateState後はリセットされているべき
    reader = await conn.runAndReadAll("SELECT value FROM rate_state WHERE bucket = 'tool'");
    rows = reader.getRowObjects() as { value: number }[];
    expect(rows[0].value).toBe(0); // リセットされているべき

    // リセット後は再度使用可能
    expect(await checkAndConsume('tool')).toBe(true);
  });

  it('rate limit should reset even with persistent DB simulation', async () => {
    const conn = await getConnection();

    // rate limitに到達
    expect(await checkAndConsume('tool')).toBe(true);
    expect(await checkAndConsume('tool')).toBe(false);

    // last_resetを過去に設定（時間窓経過をシミュレート）
    await conn.run("UPDATE rate_state SET last_reset = last_reset - 200 WHERE bucket = 'tool'");

    // initRateStateを呼び出し（デーモン再起動をシミュレート）
    await initRateState();

    // リセットされているべき
    const reader = await conn.runAndReadAll("SELECT value FROM rate_state WHERE bucket = 'tool'");
    const rows = reader.getRowObjects() as { value: number }[];
    expect(rows[0].value).toBe(0);
  });
});

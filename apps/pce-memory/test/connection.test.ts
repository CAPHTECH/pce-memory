/**
 * DB Connection Module Unit Tests
 *
 * DB接続管理のテスト:
 * - closeDb() の動作確認
 * - 冪等性の確認
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, closeDb, getConnection } from '../src/db/connection';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
});

describe('closeDb', () => {
  it('should close connection and allow reinitialization', async () => {
    // 初期化
    await initDb();
    await initSchema();

    // 接続が有効であることを確認
    const conn = await getConnection();
    const result = await conn.runAndReadAll('SELECT 1 as val');
    const rows = result.getRowObjects() as { val: number }[];
    expect(rows[0].val).toBe(1);

    // クローズ
    await closeDb();

    // 再初期化可能であることを確認
    await initDb();
    await initSchema();
    const newConn = await getConnection();
    const newResult = await newConn.runAndReadAll('SELECT 2 as val');
    const newRows = newResult.getRowObjects() as { val: number }[];
    expect(newRows[0].val).toBe(2);
  });

  it('should be idempotent (safe to call multiple times)', async () => {
    // 未初期化状態でも安全
    await closeDb();
    await closeDb();

    // 初期化後のクローズも複数回安全
    await initDb();
    await initSchema();
    await closeDb();
    await closeDb();
    await closeDb();

    // 再初期化可能
    await initDb();
    await initSchema();
    const conn = await getConnection();
    const result = await conn.runAndReadAll('SELECT 3 as val');
    const rows = result.getRowObjects() as { val: number }[];
    expect(rows[0].val).toBe(3);
  });

  it('should release resources without throwing on already closed connection', async () => {
    await initDb();
    await initSchema();

    // 接続を取得して使用
    const conn = await getConnection();
    await conn.runAndReadAll('SELECT 1');

    // closeDb は例外を投げずに完了すべき
    await expect(closeDb()).resolves.toBeUndefined();
  });
});

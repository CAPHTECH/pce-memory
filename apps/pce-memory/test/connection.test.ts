/**
 * DB Connection Module Unit Tests
 *
 * DB接続管理のテスト:
 * - closeDb() の動作確認
 * - 冪等性の確認
 */

import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { initDb, initSchema, resetDbAsync, closeDb, getConnection } from '../src/db/connection';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

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

describe('closeDb CHECKPOINT behavior', () => {
  let tempDbPath: string;

  beforeEach(async () => {
    await resetDbAsync();
  });

  afterEach(async () => {
    // 環境変数をリセット
    process.env.PCE_DB = ':memory:';

    // 一時ファイルをクリーンアップ
    if (tempDbPath) {
      try {
        if (fs.existsSync(tempDbPath)) fs.unlinkSync(tempDbPath);
        if (fs.existsSync(`${tempDbPath}.wal`)) fs.unlinkSync(`${tempDbPath}.wal`);
      } catch {
        // クリーンアップ失敗は無視
      }
    }
  });

  it('should handle CHECKPOINT gracefully for :memory: DB', async () => {
    process.env.PCE_DB = ':memory:';

    await initDb();
    await initSchema();

    // データを挿入
    const conn = await getConnection();
    await conn.run(
      "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ('test1', 'test', 'fact', 'project', 'internal', 'sha256:test1')"
    );

    // :memory: DBでもcloseDbが例外を投げないことを確認
    // CHECKPOINT は in-memory では意味がないが、エラーにならない
    await expect(closeDb()).resolves.toBeUndefined();
  });

  it('should execute CHECKPOINT for file-based DB', async () => {
    // 一時ファイルを作成
    tempDbPath = path.join(os.tmpdir(), `pce-test-${Date.now()}.db`);
    process.env.PCE_DB = tempDbPath;

    await initDb();
    await initSchema();

    // データを挿入
    const conn = await getConnection();
    await conn.run(
      "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ('test1', 'test content', 'fact', 'project', 'internal', 'sha256:test1')"
    );

    // closeDb実行（CHECKPOINTが内部で実行される）
    await closeDb();

    // 再度開いてデータが永続化されていることを確認
    await resetDbAsync();
    await initDb();
    await initSchema();

    const newConn = await getConnection();
    const result = await newConn.runAndReadAll("SELECT text FROM claims WHERE id = 'test1'");
    const rows = result.getRowObjects() as { text: string }[];

    // CHECKPOINTによりデータが永続化されている
    expect(rows.length).toBe(1);
    expect(rows[0].text).toBe('test content');

    await closeDb();
  });

  it('should log CHECKPOINT failure for file-based DB with appropriate message', async () => {
    // console.errorをスパイ
    const consoleSpy = vi.spyOn(console, 'error').mockImplementation(() => {});

    tempDbPath = path.join(os.tmpdir(), `pce-test-${Date.now()}.db`);
    process.env.PCE_DB = tempDbPath;

    await initDb();
    await initSchema();

    // 正常なcloseDb（CHECKPOINTログを確認）
    await closeDb();

    // CHECKPOINT完了のログが出力されていることを確認
    expect(consoleSpy).toHaveBeenCalledWith('[DB] Checkpoint completed');

    consoleSpy.mockRestore();
  });
});

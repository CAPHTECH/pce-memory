import { DuckDBInstance, DuckDBConnection } from '@duckdb/node-api';
import { SCHEMA_SQL } from './schema.js';

let instance: DuckDBInstance | null = null;
let cachedConnection: DuckDBConnection | null = null;

/**
 * DuckDB インスタンスを初期化（非同期）
 * 起動時に一度だけ呼び出す
 */
export async function initDb(): Promise<DuckDBInstance> {
  if (instance) return instance;
  const dbPath = process.env['PCE_DB'] ?? ':memory:';
  instance = await DuckDBInstance.create(dbPath);
  return instance;
}

/**
 * 初期化済みの DuckDB インスタンスを取得
 * initDb() が先に呼ばれている必要がある
 */
export function getDb(): DuckDBInstance {
  if (!instance) {
    throw new Error('Database not initialized. Call initDb() first.');
  }
  return instance;
}

/**
 * コネクションを取得（非同期）
 * 単一コネクションを再利用してリーク防止
 * 無効なコネクションは自動的に再作成
 */
export async function getConnection(): Promise<DuckDBConnection> {
  if (cachedConnection) {
    try {
      // コネクションが有効かを簡単なクエリで確認
      await cachedConnection.runAndReadAll('SELECT 1');
      return cachedConnection;
    } catch {
      // コネクションが無効な場合は再作成
      try {
        cachedConnection.closeSync();
      } catch {
        // クローズエラーは無視
      }
      cachedConnection = null;
    }
  }
  cachedConnection = await getDb().connect();
  return cachedConnection;
}

/**
 * スキーマを初期化（非同期）
 */
export async function initSchema() {
  const conn = await getConnection();
  const statements = SCHEMA_SQL.split(';')
    .map((s) => s.trim())
    .filter(Boolean);
  for (const stmt of statements) {
    await conn.run(stmt);
  }
}

/**
 * テスト用: DB をリセット（非同期版を推奨）
 * 互換性のため同期版も維持
 */
export function resetDb(): void {
  // 注意: この関数はコネクションを適切にクローズしない
  // 可能であれば resetDbAsync() を使用すること
  cachedConnection = null;
  instance = null;
}

/**
 * テスト用: DB をリセット（非同期）
 * コネクションを適切にクローズしてからリセット
 */
export async function resetDbAsync(): Promise<void> {
  if (cachedConnection) {
    try {
      // DuckDB Node APIはcloseSync()を使用
      cachedConnection.closeSync();
    } catch {
      // クローズエラーは無視（既にクローズされている可能性）
    }
  }
  cachedConnection = null;
  instance = null;
}

/**
 * DB接続を明示的にクローズ（デーモンシャットダウン用）
 * DuckDBロックを解放し、他のプロセスがDBにアクセスできるようにする
 */
export async function closeDb(): Promise<void> {
  if (cachedConnection) {
    try {
      cachedConnection.closeSync();
    } catch (err) {
      console.error(`[DB] Failed to close connection: ${err}`);
    }
    cachedConnection = null;
  }

  if (instance) {
    try {
      // DuckDBInstanceはcloseメソッドを持たないため、参照を解放
      // GCによってリソースが解放される
      instance = null;
    } catch (err) {
      console.error(`[DB] Failed to close instance: ${err}`);
    }
  }
}

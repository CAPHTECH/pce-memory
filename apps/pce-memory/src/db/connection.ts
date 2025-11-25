import { DuckDBInstance, DuckDBConnection } from "@duckdb/node-api";
import { readFileSync } from "fs";
import { join } from "path";

let instance: DuckDBInstance | null = null;
let cachedConnection: DuckDBConnection | null = null;

/**
 * DuckDB インスタンスを初期化（非同期）
 * 起動時に一度だけ呼び出す
 */
export async function initDb(): Promise<DuckDBInstance> {
  if (instance) return instance;
  const dbPath = process.env["PCE_DB"] ?? ":memory:";
  instance = await DuckDBInstance.create(dbPath);
  return instance;
}

/**
 * 初期化済みの DuckDB インスタンスを取得
 * initDb() が先に呼ばれている必要がある
 */
export function getDb(): DuckDBInstance {
  if (!instance) {
    throw new Error("Database not initialized. Call initDb() first.");
  }
  return instance;
}

/**
 * コネクションを取得（非同期）
 * 単一コネクションを再利用してリーク防止
 */
export async function getConnection(): Promise<DuckDBConnection> {
  if (cachedConnection) {
    return cachedConnection;
  }
  cachedConnection = await getDb().connect();
  return cachedConnection;
}

/**
 * スキーマを初期化（非同期）
 */
export async function initSchema() {
  const sql = readFileSync(join(__dirname, "schema.sql"), "utf-8");
  const conn = await getConnection();
  const statements = sql
    .split(";")
    .map((s) => s.trim())
    .filter(Boolean);
  for (const stmt of statements) {
    await conn.run(stmt);
  }
}

/**
 * テスト用: DB をリセット
 */
export function resetDb(): void {
  cachedConnection = null;
  instance = null;
}

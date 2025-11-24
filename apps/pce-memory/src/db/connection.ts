import { Database } from "@duckdb/node-api";
import { readFileSync } from "fs";
import { join } from "path";

let db: Database | null = null;

export function getDb() {
  if (db) return db;
  const dbPath = process.env.PCE_DB ?? ":memory:";
  db = new Database(dbPath);
  return db;
}

export function initSchema() {
  const sql = readFileSync(join(__dirname, "schema.sql"), "utf-8");
  const conn = getDb().connect();
  sql
    .split(";")
    .map((s) => s.trim())
    .filter(Boolean)
    .forEach((stmt) => conn.run(stmt));
  conn.close();
}

-- Minimal DuckDB schema (placeholder)
CREATE TABLE IF NOT EXISTS claims (
  id TEXT PRIMARY KEY,
  text TEXT NOT NULL,
  kind TEXT NOT NULL,
  scope TEXT NOT NULL,
  boundary_class TEXT NOT NULL,
  content_hash TEXT UNIQUE NOT NULL
);

CREATE TABLE IF NOT EXISTS active_contexts (
  id TEXT PRIMARY KEY,
  claims JSON
);

CREATE TABLE IF NOT EXISTS logs (
  id TEXT PRIMARY KEY,
  op TEXT,
  ts TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  ok BOOLEAN,
  req TEXT
);

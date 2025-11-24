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
  req TEXT,
  trace TEXT,
  policy_version TEXT
);

CREATE TABLE IF NOT EXISTS feedback (
  id TEXT PRIMARY KEY,
  claim_id TEXT NOT NULL,
  signal TEXT NOT NULL,
  score DOUBLE,
  ts TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

CREATE TABLE IF NOT EXISTS rate_state (
  bucket TEXT PRIMARY KEY,
  value INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS critic (
  claim_id TEXT PRIMARY KEY,
  score DOUBLE NOT NULL
);

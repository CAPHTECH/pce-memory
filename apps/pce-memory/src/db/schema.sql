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
  value INTEGER NOT NULL,
  last_reset INTEGER DEFAULT (epoch(now())::INTEGER)
);

CREATE TABLE IF NOT EXISTS critic (
  claim_id TEXT PRIMARY KEY,
  score DOUBLE NOT NULL
);

-- ポリシー永続化テーブル（ADR-0002対応）
-- "Latest wins" 戦略: created_at DESC で最新を取得
CREATE TABLE IF NOT EXISTS policies (
  id TEXT PRIMARY KEY,
  version TEXT NOT NULL,
  yaml_content TEXT NOT NULL,
  config_json JSON NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

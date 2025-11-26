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

-- 埋め込みキャッシュテーブル（ADR-0003対応）
-- TLA+ Inv_CacheVersionConsistency: キャッシュキー = text_hash + model_version
CREATE TABLE IF NOT EXISTS embedding_cache (
  text_hash TEXT NOT NULL,
  model_version TEXT NOT NULL,
  embedding DOUBLE[] NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (text_hash, model_version)
);

-- ========== ADR-0004: Hybrid Search対応 ==========

-- Claim埋め込みベクトル保存テーブル
-- TLA+ Inv_C_MergeComplete: ベクトル検索候補を保持
-- Note: DuckDBはFOREIGN KEY CASCADEをサポートしないため、参照制約のみ定義
CREATE TABLE IF NOT EXISTS claim_vectors (
  claim_id TEXT PRIMARY KEY REFERENCES claims(id),
  embedding DOUBLE[] NOT NULL,
  model_version TEXT NOT NULL,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);
CREATE INDEX IF NOT EXISTS idx_claim_vectors_claim_id ON claim_vectors(claim_id);

-- コサイン類似度計算マクロ
-- TLA+ claimVecRelevant: cos_sim >= threshold で判定
CREATE MACRO IF NOT EXISTS cos_sim(a, b) AS (
  list_sum(list_transform(list_zip(a, b), x -> x[1]*x[2]))
  / NULLIF(sqrt(list_sum(list_transform(a, x -> x*x))), 0)
  / NULLIF(sqrt(list_sum(list_transform(b, x -> x*x))), 0)
);

-- ハイブリッドスコア融合マクロ（α=0.65デフォルト）
-- TLA+ FusedScore: α × vecScore + (1-α) × textScore
CREATE MACRO IF NOT EXISTS hybrid_score(text_score, vec_score, alpha) AS
  alpha * vec_score + (1.0 - alpha) * text_score;

-- コサイン類似度を0-1正規化マクロ
-- cos_sim範囲[-1, 1]を[0, 1]に変換
CREATE MACRO IF NOT EXISTS norm_cos(sim) AS (sim + 1.0) / 2.0;

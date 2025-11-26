-- Minimal DuckDB schema (placeholder)
CREATE TABLE IF NOT EXISTS claims (
  id TEXT PRIMARY KEY,
  text TEXT NOT NULL,
  kind TEXT NOT NULL,
  scope TEXT NOT NULL,
  boundary_class TEXT NOT NULL,
  content_hash TEXT UNIQUE NOT NULL,
  -- g()再ランキング用カラム（ADR-0004準拠）
  utility REAL DEFAULT 0.0,
  confidence REAL DEFAULT 0.5,
  created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
  -- recency計算の基準時刻（positive feedbackでのみ更新）
  recency_anchor TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- ランキング用インデックス（g()計算最適化）
CREATE INDEX IF NOT EXISTS idx_claims_ranking
ON claims(utility, confidence, updated_at, created_at);

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

-- ========== g()再ランキング関数（activation-ranking.md準拠） ==========

-- シグモイド関数
-- TLA+ σ(x): 0-1正規化
CREATE MACRO IF NOT EXISTS sigmoid(x) AS 1.0 / (1.0 + exp(-x));

-- recency_decay関数（kind別半減期対応）
-- TLA+ Inv_RecencyMonotonicity: 時間経過で単調減少
-- 半減期: fact=120d, task=14d, preference=90d, policy_hint=365d, default=30d
CREATE MACRO IF NOT EXISTS recency_decay(ts, kind) AS (
  exp(-0.693147 * (epoch(now()) - epoch(ts)) / 86400.0
    / CASE kind
        WHEN 'fact' THEN 120.0
        WHEN 'task' THEN 14.0
        WHEN 'preference' THEN 90.0
        WHEN 'policy_hint' THEN 365.0
        ELSE 30.0
      END)
);

-- g()再ランク係数
-- TLA+ Inv_RangeBounds: g ∈ [0.09, 1.0]
-- g = (0.6 + 0.4σ(utility_z)) × (0.5 + 0.5c) × (0.3 + 0.7r)
-- 引数tsはrecency_anchorを渡す（positive feedbackでのみ更新）
CREATE MACRO IF NOT EXISTS g_rerank(utility_z, confidence, ts, kind) AS (
  (0.6 + 0.4 * sigmoid(utility_z))
  * (0.5 + 0.5 * LEAST(1.0, GREATEST(0.0, confidence)))
  * (0.3 + 0.7 * LEAST(1.0, GREATEST(0.0, recency_decay(ts, kind))))
);

# DuckDB 検索拡張ガイド — FTS / VSS とハイブリッド検索

> **目的**：`pce‑memory` の検索品質とスループットを強化するため、DuckDB の **FTS（全文検索）** / **VSS（ベクトル近傍探索）** を導入・運用する手引き。  
> まずは拡張無し（`ILIKE` + `cos_sim` マクロ）で成立させ、段階的に FTS/VSS を追加する。

- スキーマ本体は `docs/schema.md`（DuckDB v0）を参照。  
- 境界・ポリシー・ハイブリッド係数は `boundary-policy.md` / `activation-ranking.md`（後述）に準拠。  

---

## 1. サマリー（どの方式をいつ使うか）

| レベル | 方式 | 依存 | 長所 | 短所 | 典型スループット感 | 推奨用途 |
|---|---|---|---|---|---|---|
| L0 | `ILIKE` + 正規化 | なし | 導入不要・常駐不要 | 品質・速度は限定的 | 10⁴~10⁵ トークン/秒級 | 小規模・最初の MVP |
| L1 | `cos_sim`（LIST[Double]）全件走査 | なし | 拡張なしでベクトル検索 | N が大きいと遅い | 10³~10⁴ ベクトル/秒 | 1〜10 万件未満の原型運用 |
| L2 | **FTS** 拡張 | `INSTALL fts` | 高速・ランキング（BM25 相当） | 拡張導入が必要 | 10⁵~10⁶ トークン/秒級 | コーパスが増えたら |
| L3 | **VSS** 拡張（HNSW/IVF 等） | `INSTALL vss` | 大規模ベクトル即時検索 | 近似・チューニング必要 | 10⁵~10⁶ ベクトル/秒級 | 10万件超のベクトル検索 |

> **ハイブリッド**：L2（FTS）と L1/L3（ベクトル）を **α 混合**。既定 α=**0.65** を推奨（`activation-ranking.md` 参照）。

### 1.1 既定パラメータ（初期値）

- α（融合比）: **0.65**（推奨レンジ 0.3〜0.9）
- k_final: **12**（UI/プロンプト許容量に合わせる）
- k_txt: **48**（k_final の 3〜5 倍）
- k_vec: **96**（k_final の 6〜10 倍。VSS のときは 1.5〜2.0 倍に抑える）
- Recency 半減期 HL: **30 日**（ドメインにより 7〜90 日で調整）
- timeout: **15s**（activate 全体の既定。search 単体は 10s）

---

## 2. 依存確認とインストール

```sql
-- まずは拡張無しで動かし、必要になった段階で導入
-- FTS
INSTALL fts;   -- 一度だけ
LOAD fts;      -- セッションごと

-- VSS（ベクトル近傍探索）
INSTALL vss;   -- 一度だけ
LOAD vss;      -- セッションごと

-- 現在ロードされている拡張を確認
SELECT * FROM duckdb_extensions();
```

> **注意**：DuckDB の拡張はバージョンにより DDL/DML シンタックスが異なることがあります。以下の VSS/FTS の DDL/クエリ例は **概念図（擬似文法）**も含みます。利用しているバージョンのドキュメントで最終確認してください。

---

## 3. テキスト検索

### 3.1 拡張なしの簡易検索（既定）

```sql
-- 正規化 + ILIKE。事前にアプリ側で全角/半角・大文字小文字を正規化すること。
SELECT id, text
FROM claims
WHERE lower(text) LIKE '%' || lower(:q) || '%'
  AND scope IN ('session','project','principle')
ORDER BY created_at DESC
LIMIT :k;
```

### 3.2 FTS 拡張を使う（概念図）

1) 拡張ロード：`INSTALL fts; LOAD fts;`
2) インデックス作成（**擬似文法**：実際のシンタックスは利用バージョンに合わせてください）

```sql
-- PSEUDO: FTS インデックスの作成（実際の構文は拡張ドキュメントで確認）
-- 例：claims(text) を対象に FTS インデックス claim_fts を作る
-- CREATE INDEX claim_fts ON claims USING fts(text);
```

3) 検索（**擬似文法**）

```sql
-- PSEUDO: FTS 検索 + スコア取得
-- SELECT id, fts_score AS bm25
-- FROM claims
-- WHERE fts_match(text, :q)
-- ORDER BY fts_score DESC
-- LIMIT :k;
```

> **運用**：FTS インデックスは bulk 取り込み後に `REINDEX`/`REFRESH` を実行。低トラフィック時にバッチ更新するのが安全。

#### 3.3 FTS（最小ガイド）

- まず `INSTALL fts; LOAD fts;`
- claims(text) を対象に FTS インデックスを作成（実際のシンタックスはバージョン依存）
- 日本語は ILIKE より **事前トークン化（形態素 or n-gram）** を併用
- バルク更新後は `REINDEX/REFRESH`。負荷の低い時間帯に実行

## 3x. 日本語テキストの前処理（最低限）

- 正規化: 大文字小文字・全角半角・記号の正規化を **アプリ層**で行い `normalized_text` に保存
- n-gram: 形態素がない場合は 2-gram/3-gram を `normalized_text` から生成して検索に併用
- 禁止語: 境界ポリシーで禁止トークンを定義し、FTS/ILIKE の前に除去（prompt injection 抵抗を上げる）

---

## 4. ベクトル検索

### 4.1 拡張なし：`cos_sim` マクロ + 全件スキャン

`docs/schema.md` の `1.1 SQL マクロ（ベクトル類似）` で定義した `cos_sim(a,b)` を使用します。

```sql
-- :qvec は LIST<DOUBLE>（埋め込み）
SELECT v.claim_id,
       cos_sim(v.embedding, :qvec) AS sim
FROM claim_vectors AS v
JOIN claims AS c ON c.id = v.claim_id
WHERE c.scope IN ('session','project','principle')
ORDER BY sim DESC
LIMIT :k;
```

### 4.2 VSS 拡張：近似近傍（概念図）
>
> **擬似文法**。実装やパラメータ名（`metric`, `ef_search`, `M` など）は拡張のバージョンにより異なります。

```sql
-- インデックス作成（HNSW/IVF 等）
-- PSEUDO: CREATE INDEX idx_claim_vec ON claim_vectors USING vss(embedding) WITH (metric='cosine', m=16, ef_construction=200);

-- 検索
-- PSEUDO: SELECT claim_id, vss_distance(embedding, :qvec) AS dist
--         FROM claim_vectors
--         USING INDEX idx_claim_vec
--         ORDER BY dist ASC
--         LIMIT :k;
```

> **チューニングの目安**：
>
> - HNSW：`M`（グラフの分岐数）= 8〜32、`ef_search` はレイテンシに応じて 64→256
> - コサイン距離に統一（`cos_sim` を `1−sim` に変換すると整合が取りやすい）

#### 4.3 VSS（最小ガイド）

- `INSTALL vss; LOAD vss;`
- `CREATE INDEX ... USING vss(embedding) WITH (metric='cosine', ...)`
- HNSW の目安: `M=16` / `ef_search=64〜256`。レイテンシと recall のトレードオフで調整
- 埋め込みモデル更新時は `claim_vectors.version` で世代を分け段階的に再生成

## 4x. スコア正規化・融合・再ランク（定義）

- Text 正規化:
  - FTS あり: `S_text = (bm25 - bm25_min) / max(bm25_max - bm25_min, ε)`（候補集合での min-max）
  - FTS なし: `S_text = 1 / (1 + rank)`（rank は ILIKE の順位, 1 始まり）
- Vector 正規化:
  - cos 類似 `sim ∈ [-1,1]` を `S_vec = (sim + 1) / 2` に写像
- 再ランク関数 g（既定）:
  - `g = (0.6 + 0.4 * σ(utility_z)) * (0.5 + 0.5 * confidence) * (0.3 + 0.7 * recency(ts))`
  - `σ(x) = 1/(1+exp(-x))`、`utility_z` は z 正規化（なければ 0–1 線形正規化）
  - `recency(ts) = exp( - ln(2) * age_days / HL )`、`HL` は半減期（既定 30 日）
- 融合:
  - `S = α * S_vec + (1 - α) * S_text`（既定 `α = 0.65`）
  - 最終スコア: `score_final = S * g`

---

## 5. ハイブリッド検索（FTS × ベクトル）

### 5.1 スコア融合の基本式

- `S_text = normalize(bm25)`  （FTS が無い場合は簡易スコア `1/(1+rank)` 等）
- `S_vec  = normalize(sim)`   （`sim` は 0〜1 に正規化）
- **融合**：`S = α * S_vec + (1 − α) * S_text`、既定 **α = 0.65**

### 5.2 クエリ雛形（FTS あり / なし両対応）

```sql
-- 前段：text 側候補のサブクエリ（FTSが無ければ ILIKE に置換）
WITH txt AS (
  SELECT id, /*PSEUDO: fts_score */ 1.0 AS s_text
  FROM claims
  WHERE /* PSEUDO: fts_match(text, :q) */ lower(text) LIKE '%'||lower(:q)||'%'
  AND scope IN ('session','project','principle')
  LIMIT :k_txt
),
vec AS (
  SELECT v.claim_id AS id, cos_sim(v.embedding, :qvec) AS s_vec
  FROM claim_vectors v JOIN claims c ON c.id=v.claim_id
  WHERE c.scope IN ('session','project','principle')
  LIMIT :k_vec
),
joined AS (
  SELECT coalesce(t.id, v.id) AS id,
         coalesce(t.s_text, 0) AS s_text,
         coalesce(v.s_vec, 0)  AS s_vec
  FROM txt t FULL OUTER JOIN vec v ON t.id = v.id
)
SELECT j.id,
       (:alpha) * j.s_vec + (1-:alpha) * j.s_text AS score
FROM joined j
ORDER BY score DESC
LIMIT :k_final;
```

#### 5.3 実用クエリ雛形（FTS なしでも可）

```sql
-- 入力: :q (TEXT), :qvec (LIST<DOUBLE>), :k_txt, :k_vec, :k_final, :alpha
WITH txt AS (
  SELECT id, 1.0 / (1.0 + ROW_NUMBER() OVER (ORDER BY created_at DESC)) AS s_text
  FROM claims
  WHERE lower(text) LIKE '%'||lower(:q)||'%'
    AND scope IN ('session','project','principle')
  LIMIT :k_txt
),
vec AS (
  SELECT v.claim_id AS id, norm_cos(cos_sim(v.embedding, :qvec)) AS s_vec
  FROM claim_vectors v JOIN claims c ON c.id=v.claim_id
  WHERE c.scope IN ('session','project','principle')
  LIMIT :k_vec
),
joined AS (
  SELECT coalesce(t.id, v.id) AS id,
         coalesce(t.s_text, 0) AS s_text,
         coalesce(v.s_vec, 0)  AS s_vec
  FROM txt t FULL OUTER JOIN vec v ON t.id = v.id
),
ranked AS (
  SELECT j.id, (:alpha) * j.s_vec + (1-:alpha) * j.s_text AS S FROM joined j
)
SELECT c.id,
       (r.S) *
       (0.6 + 0.4 * 1/(1+exp(-c.utility))) *
       (0.5 + 0.5 * c.confidence) *
       (0.3 + 0.7 * recency_decay(c.created_at, 30)) AS score_final
FROM ranked r
JOIN claims c ON c.id=r.id
ORDER BY score_final DESC
LIMIT :k_final;
```

> **α** は `activation-ranking.md` の既定（0.65）を利用。コーパスやジャンルで学習する場合は Grid Search/ベイズ最適化で更新。

---

## 6. `r(q, C^L, B, policy, critic)` への組み込み

`activation`（AC 生成）関数は以下の順序で評価する：

1. **Boundary 前置フィルタ**：`scope/allow/boundary_class/I(B)` を先に絞る（`boundary-policy.md`）。
2. **テキスト候補**：FTS（なければ ILIKE）で `k_txt` 件。
3. **ベクトル候補**：`cos_sim` or VSS で `k_vec` 件。
4. **融合**：前節の `S` に従い α 混合。
5. **再ランク**：`g(utility, confidence, recency)` を乗算（`activation-ranking.md`）。
6. **AC 構成**：`active_contexts / active_context_items` に `rank/score` を保存。

---

## 7. メンテナンスと更新

- **FTS**：大量 upsert 後は `REINDEX/REFRESH`。小さな変更はバッファリングしてからバルク更新。  
- **VSS**：インデックス再構築のバッチウィンドウを確保。`ef_search` を負荷・レイテンシに合わせて調整。
- **ベクトル**：埋め込みモデルを更新した場合は `claim_vectors` を再生成（旧ベクトルは `version` 列で切り替え）。

---

## 8. ベンチマーク（最小の回し方）

1. **データ分割**：`claims` を 8:1:1 に分割（train/valid/test）。
2. **擬似クエリ集合**：`test` の各 `text` から n‑gram を抽出してクエリ集合 Q を作る。ベクトルは `E(text)`。
3. **ゴールド**：`relations`（例えば `mentions`/`depends_on`）やヒューマンアノテーションで正解集合 G を持つ。
4. **計測**：各方式（L0/L1/L2/L3/Hybrid）で **Recall@k / nDCG@k / p50/p90 レイテンシ** を取得。
5. **α チューニング**：Grid Search（0.3〜0.9 step=0.05）で最良 α を記録。

> 記録は `events(topic='benchmark')` に保存。KPI 連携は `observability.md` 参照。

### 8.1 合格ライン（例）

- Recall@12 ≥ **0.70**（valid セット）
- nDCG@12 ≥ **0.45**
- activate p90 レイテンシ ≤ **1500ms**（L2+L1 ハイブリッド）
- 逸脱監査: `events(topic='search_fallback') / events(topic='search') ≤ 1%`

---

## 9. フォールバック戦略とエラーハンドリング

- **拡張未導入**：`LOAD fts/vss` が失敗したら自動で L0/L1 にフォールバック。`events` に `topic='search_fallback'` を記録。
- **空振り**：テキスト/ベクトルのどちらかが 0 件でも `FULL OUTER JOIN` で穴埋め → もう一方のスコアで返す。
- **過度の近傍数**：VSS の k を大きくしすぎるとレイテンシが悪化。`k_vec` は `k_final` の 1.5〜2.0 倍が目安。
- **距離/類似の統一**：VSS の距離を採用する場合は `sim = 1 - dist` の写像で **コサイン基準**に統一し、融合前に正規化する。

---

## 10. セキュリティ・境界との整合

- すべての候補選択は **事前に** `scope/allow/boundary_class/I(B)` で絞り込み（`boundary-policy.md`）。
- ベクトル埋め込みの前に **Redact-before-Send**（外部埋め込みを使う場合）。
- 監査：`events` に `request_id/trace_id/policy_version` を保存。FTS/VSS での例外も記録。

---

## 11. 既知の落とし穴（FAQ）

- **ILIKE の品質が足りない**：まずは FTS を導入。日本語は形態素解析ベースの前処理を推奨。
- **VSS の類似度と cos_sim の値域が違う**：`sim ↔ 1−dist` の変換式を整理。混在時は **コサイン基準に統一**。
- **DuckDB の書き込み競合**：単一プロセス書き込みが前提。MCP stdio モデルでは自然に満たすが、並列ワーカーはキューイングする。

---

## 12. 参考

- `docs/schema.md` — DuckDB スキーマ（TIMESTAMP、cos_sim、AC/LCP ほか）
- `boundary-policy.md` — Boundary/Policy/precedence/Redact
- `activation-ranking.md` — α/β・再ランク関数 g() の仕様（作成予定）

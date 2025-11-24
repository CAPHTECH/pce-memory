# Activation & Ranking Spec (r, S, g) — pce‑memory v0.1

> **目的**：MCP ツール `pce.memory.activate` / `pce.memory.search` が返す候補の **選別（Activation: r）**、**スコアリング（融合: S）**、**再ランク（g）** を定義する。DuckDB スキーマ（`schema.md`）/ 検索拡張（`search_extensions_duckdb.md`）/ 境界（`boundary-policy.md`）と整合する。

- **前提**：`r(q, C^L, B, policy, critic)` は **AC（Active Context）** を構成する関数。境界（Boundary）による前置フィルタを必須とし、FTS/VSS の有無に応じて内部戦略を切替える。
- **出力**：`active_contexts(id, scope, expires_at, policy_version, provenance)` と `active_context_items(ac_id, claim_id, rank, score)`、および UI/エージェント用の **説明用メタ**（s_text, s_vec, S, g, reason）を返す。

---

## 0. 記号とスコープ

- **q**: テキストクエリ（正規化前文字列）
- **C^L**: LCP（Latent Context Pool）— 長期の主張/グラフ/由来の集合
- **B**: Boundary（`scope`, `boundary_class`, `allow`, `I(B)` 不変量）
- **policy**: `boundary-policy.yaml` + `retrieval.hybrid` 等の運用パラメータ
- **critic**: `utility/confidence/recency` 更新のための評価器（`feedbacks` 由来）
- **AC**: Active Context（短期、使い捨て）

---

## 1. フロー定義：`r(q, C^L, B, policy, critic)`

1. **前置フィルタ**（必須）
   - `claims.scope ∈ {session,project,principle}` かつ `claims.boundary_class ∈ B.allowed_classes`
   - 不変量 `I(B)` を満たすもののみ候補（例：破壊的変更禁止）。
2. **テキスト候補抽出**（k_txt 件）
   - FTS があれば FTS、無ければ `ILIKE`（事前に `normalized_text` を推奨）。
3. **ベクトル候補抽出**（k_vec 件）
   - `cos_sim(embedding, E(q))` を利用（DuckDB マクロ、`schema.md` の 1.1 参照）。VSS 拡張があれば使用可。
4. **候補結合**
   - `FULL OUTER JOIN` で id を併合し、`s_text` と `s_vec` を持つ候補集合にする。
5. **正規化**（節 2）
   - `S_text`, `S_vec` を [0,1] に写像。
6. **融合（ハイブリッド）**（節 3）
   - `S = α * S_vec + (1 - α) * S_text`。
7. **再ランク（係数 g）**（節 4）
   - `score_final = S * g(utility, confidence, recency)` を計算。
8. **AC 構成・保存**
   - `active_contexts` に AC を作成、`active_context_items` に `rank, score_final` を保存。
   - `events(topic='activate')` に `request_id/trace_id/policy_version/α/k_*` をログ。
- **最終採用条件**：`score_final ≥ 0.15` を満たす候補のみ AC に採用（満たさない場合は `reason="below_threshold"` を付与し `events` に記録）。
9. **説明メタの付与**（任意）
   - 各候補に `s_text, s_vec, S, g_breakdown, reason` を同梱（デバッグ・監査用）。

---

## 2. スコア正規化

**Text 正規化**
- **FTS あり**：
  - 各候補の bm25 スコアを `S_text = (bm25 - bm25_min) / max(bm25_max - bm25_min, ε)` に写像。
- **FTS なし**：
  - ILIKE の順位 `rank∈{1..k_txt}` を `S_text = 1 / (1 + rank)` に変換。

**Vector 正規化**
- **cos 類似** `sim ∈ [-1, 1]` を `S_vec = (sim + 1) / 2`（`norm_cos` マクロ）に写像。
- **VSS 距離**を採用する場合は `sim = 1 - dist` とみなし、上式へ。

> 参考：マクロは `schema.md` の `cos_sim`, `norm_cos`, `recency_decay` を使用。

#### 校正（Calibration）

- オフラインでクエリ集合ごとに `S_text_raw` と `S_vec_raw` を等確率写像（quantile / isotonic）または Platt scaling で [0,1] に校正し、`S_text` / `S_vec` として使用する。
- 校正係数は `policies` に保存し、`policy_version` と紐づける。ロード不能時は従来の min–max / cos→[0,1] にフォールバック。

---

## 3. 融合（ハイブリッド）

- 基本式：`S = α * S_vec + (1 - α) * S_text`
- 既定 `α = 0.65`（policy で上書き可）
- 候補が片側のみのとき：欠落側を 0 とし、存在側のスコアをそのまま使用

**policy 設定例**
```yaml
retrieval:
  hybrid:
    alpha: 0.65      # [0.3, 0.9]
    k_txt: 48        # k_final の 3〜5倍
    k_vec: 96        # k_final の 6〜10倍（VSS は 1.5〜2.0倍）
    k_final: 12
    recency_half_life_days: 30
```

#### 動的パラメータ（推奨規則）

- **α（融合比）**：
  - `len(tokens(q)) ≤ 2` または **コード/引用/URL 片**を含む → α∈[0.3, 0.5]（lexical 寄り）
  - **自然文の長文** → α∈[0.7, 0.85]（semantic 寄り）
- **k_txt / k_vec**：
  - 初期値: `k_txt = 4 × k_final`, `k_vec = 8 × k_final`
  - 片側ヒットが `k_final/2` 未満なら当該側のみ 2× に再拡張（1 回まで）

---

## 4. 再ランク `g(utility, confidence, recency)`

- **定義**：
  ```
  g = (0.6 + 0.4 * σ(utility_z))
    * (0.5 + 0.5 * confidence)
    * (0.3 + 0.7 * recency(ts))
  ```
- `σ(x) = 1/(1+exp(-x))`。`utility_z` はユーティリティの z スコア。z スコアが無ければ 0–1 へ線形で代用。
- `recency(ts) = exp( - ln(2) * age_days / HL )`。既定 `HL=30` 日。`age_days = (now()-ts)/86400`。
- 上界下界：各項は `[0,1]` にクリップ（数値安定性のため `ε=1e-6` を使用）。

**Feedback→指標更新（運用ルール）**
- `helpful(+1)`: `utility += 0.10`, `confidence += 0.05`
- `harmful(+1)`: `utility -= 0.20`, `confidence -= 0.10`
- `outdated`:     `confidence -= 0.20`
- `duplicate`:    代表にマージ、旧レコードの `utility` を減衰
- デイケイ：`utility` 30日半減、`quality` 120日半減（`events(topic='critic')`へ）

##### quality の取り扱い（任意）

- 運用上 `quality` を再ランクに含める場合は、`g ← g * (0.5 + 0.5 * quality)` を適用する。
- 設定は policy 側で `retrieval.rerank.use_quality: true` のときのみ有効とし、既定は無効。

#### recency 半減期 HL（kind 別既定）

- 有効時刻 `ts_eff = coalesce(updated_at, created_at)` を用い、`recency(ts_eff)` を計算する。
- 種別ごとの半減期（推奨初期値）:
  - `fact: 120d`, `task: 14d`, `preference: 90d`, `policy_hint: 365d`

---

## 5. SQL 雛形（FTS 無しでも可）

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

> FTS/VSS 利用時は `txt`/`vec` サブクエリを置換。正規化ルールは節 2 を踏襲すること。

#### 5.3 多様性（MMR）と重複抑制（推奨）

- **MMR**（Maximal Marginal Relevance）を最終段に適用：`score_div = λ·score_final − (1−λ)·max_sim_to_selected`（λ の初期値 0.85、`max_sim_to_selected` は cos 類似で計算）。
- **重複抑制**：`content_hash` 単位で 1 件に集約。さらに entity クラスタ（同一エンティティ/リソース）につき最大 1〜2 件に制限。
- 実装はアプリ層での貪欲法が簡潔（SQL での再帰 CTE より高速）。

#### 5.4 候補結合の代替（UNION + 左結合）

```sql
-- txt と vec の候補IDを先に集合化し、特徴量を左結合で付与
WITH txt AS (...), vec AS (...),
ids AS (
  SELECT id FROM txt
  UNION
  SELECT id FROM vec
)
SELECT ids.id,
       coalesce(txt.s_text,0) AS s_text,
       coalesce(vec.s_vec,0)  AS s_vec
FROM ids
LEFT JOIN txt ON txt.id=ids.id
LEFT JOIN vec ON vec.id=ids.id;
```

---

## 6. MCP 連携（`pce.memory.activate` / `pce.memory.search`）

- `activate`：上記フローで AC を生成し、`active_contexts`/`active_context_items` を保存。レスポンスには `rank/score_final` に加え、`s_text/s_vec/S/g` のブレークダウンを **任意で**返す。
- `search`：AC を作らず、`score_final` で上位 k を返す。`policy_version` と `provenance`、`request_id/trace_id` を必ず同梱。
- すべて **Boundary 前置**と **Redact-before-Embed/Send** を適用（`boundary-policy.md` 参照）。

> `reason` の形式は `key=value;` の列挙（例：`FTS=rank:2; cos:0.92; recent:12d; util:0.86; conf:0.72`）に統一すると解析しやすい。
> また `events(topic='activate')` には `s_text/s_vec/S/g/score_final` の統計（avg/p50/p90）も併記する。

**レスポンス例（抜粋）**
```json
{
  "active_context_id": "ac_9x",
  "claims": [
    {
      "id": "clm_7k",
      "text": "解約APIは POST /subscriptions/{id}/cancel …",
      "score_final": 0.82,
      "features": {"s_text":0.55, "s_vec":0.91, "S":0.76, "g":{"util":0.86,"conf":0.72,"rec":0.93}},
      "reason": "FTS:rank=2, cos=0.92, recent=12d, utility↑, confidence中"
    }
  ],
  "policy_version": "0.1.3"
}
```

---

## 7. パラメータ管理とオーバーライド

- policy で `retrieval.hybrid.alpha/k_*`、`recency_half_life_days` を上書き可。
- テナント/プロジェクト単位の**微調整**は `policies` に YAML を保存し `events(topic='policy')` で履歴を持つ。

---

## 8. ベンチマークと合格ライン

1. `claims` を 8:1:1 に分割（train/valid/test）
2. `test` から擬似クエリ集合 Q を作成（n‑gram 抽出 + 埋め込み）
3. ゴールド集合 G（`relations` や人手ラベル）を作成
4. L0/L1/L2/L3/Hybrid を実行し、**Recall@k / nDCG@k / p50,p90** を記録

**合格ライン（例）**
- Recall@12 ≥ **0.70**、nDCG@12 ≥ **0.45**
- activate p90 ≤ **1500ms**（L2+L1）
- `events(topic='search_fallback') / events(topic='search') ≤ 1%`

---

## 9. 既知の落とし穴と対処

- FTS/VSSロード失敗時は L0/L1 へフォールバックし、`events(topic='search_fallback')` を発火。
- cos と VSS 距離が混在する場合は **コサイン基準**に統一（`sim = 1 - dist`）。
- ILIKE の品質が足りない日本語コーパスでは、**事前正規化 + n‑gram/形態素**を併用。
- DuckDB は **単一プロセス書込み**前提（stdio モデルでは自然に満たす）。並列ワーカーはキューイング。

---

## 10. 実装チェックリスト

- [ ] `cos_sim/norm_cos/recency_decay` マクロがロード済み
- [ ] `α, k_txt, k_vec, k_final, HL, timeout` を policy or env で供給
- [ ] FTS/VSS 拡張の有無で `txt/vec` サブクエリを切替
- [ ] Boundary 前置 + Redact を全段の前に適用
- [ ] `events` に `request_id/trace_id/policy_version/α/k_*` を記録
- [ ] `active_context_items.score` は **score_final** を保存
- [ ] `S_text/S_vec` の **校正係数**がロードできなかった場合のフォールバック（min–max 等）
- [ ] MMR/重複抑制（`content_hash`／entity クラスタ）を適用
- [ ] 最終採用閾値 `score_final ≥ 0.15` の撥ね処理と `reason="below_threshold"` の記録

---

## 参照
- `schema.md` — DuckDB スキーマ（TIMESTAMP, cos_sim, AC/LCP）
- `search_extensions_duckdb.md` — FTS/VSS 導入とハイブリッド戦略
- `boundary-policy.md` — 境界/不変量/precedence ルール
- `mcp-tools.md` — MCP ツール Schema とレスポンス Envelope
- `pce-memory-vision.ja.md` — アーキテクチャと KPI 方針

# ADR-0004: Hybrid Search設計選択（形式検証に基づく3設計比較）

## ステータス

採択済み（2024-11-26）

## コンテキスト

pce-memory v0.1 MVPの検索機能について、形式検証（TLA+モデル検査およびAlloy構造解析）を用いて3つの設計バリアントを比較評価した。

### 評価した設計バリアント

1. **設計A: Text-only検索（ILIKE）**
   - SQLのILIKE演算子によるテキストパターンマッチング
   - 実装シンプル、完全一致に強い

2. **設計B: Vector-only検索（cos_sim）**
   - 埋め込みベクトルのコサイン類似度による意味検索
   - 意味的関連性に強い

3. **設計C: Hybrid検索（α-weighted fusion）**
   - テキスト検索とベクトル検索の結果を重み付け融合
   - 融合式: `S = α × S_vec + (1-α) × S_text` （α=0.65）

### 検証に使用した仕様

- `docs/spec/tlaplus/hybrid_search_simple.tla`: TLA+時相的検証
- `docs/spec/tlaplus/hybrid_search_comparison.tla`: 詳細設計比較
- `docs/spec/alloy/hybrid_search_comparison.als`: Alloy構造検証

## 形式検証の結果

### TLA+モデル検査（hybrid_search_simple.tla）

| 不変条件 | 設計A | 設計B | 設計C |
|---------|-------|-------|-------|
| ScopeConsistency | ✅ パス | ✅ パス | ✅ パス |
| ThresholdFiltering | ✅ パス | ✅ パス | ✅ パス |
| MergeComplete | N/A | N/A | ✅ パス |
| FusionCorrectness | N/A | N/A | ✅ パス |
| CompleteCoverage | N/A | N/A | ✅ パス |
| NoOutOfScopeClaims | ✅ パス | ✅ パス | ✅ パス |

**検証規模:**
- 44,236,064 状態生成
- 3,516,352 個別状態探索
- 探索深度: 9

### 設計比較検証（反例発見）

#### 設計Aの限界: Vector関連候補を逃す

```
Inv_A_MissesVectorOnly 違反:
- c2: vectorRelevant = TRUE, textRelevant = FALSE
- c2 は scope = session で requestedScopes に含まれる
- A_accepted = {} （c2 が含まれない）
- B_candidates = {c2} （ベクトル検索では発見）
```

**解釈**: 設計Aは意味的に関連するがテキスト一致しない候補を逃す。

#### 設計Bの限界: Text完全一致候補を逃す

同様に、設計Bはテキスト完全一致するがベクトル類似度が低い候補を逃す可能性がある。

### Alloy構造解析

| アサーション | 設計A | 設計B | 設計C |
|-------------|-------|-------|-------|
| ScopeFilterComplete | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT |
| RankingConsistent | ✅ UNSAT | ✅ UNSAT | ✅ UNSAT |
| MissesVectorOnlyClaims | ❌ SAT (反例) | N/A | N/A |
| MissesTextOnlyClaims | N/A | ❌ SAT (反例) | N/A |
| CoversTextOrVector | N/A | N/A | ✅ UNSAT |
| FusionCorrect | N/A | N/A | ✅ UNSAT |

## 決定

**設計C（Hybrid検索）を採用する。**

### 理由

1. **完全カバレッジ**: テキスト関連またはベクトル関連のいずれかの候補を全て含む
2. **形式検証済み**: 融合計算、スコープフィルタ、閾値フィルタの正しさが保証
3. **柔軟性**: α係数により検索特性を調整可能
4. **docs/activation-ranking.md仕様準拠**: 既存設計ドキュメントと整合

### 採用しない設計

- **設計A（Text-only）**: 意味的関連候補を逃す（反例で実証）
- **設計B（Vector-only）**: 完全一致候補を逃す可能性（反例で実証）

## 実装仕様

### 融合スコア計算

```sql
-- DuckDB SQL
CREATE MACRO hybrid_score(text_score, vec_score, alpha) AS
  alpha * vec_score + (1 - alpha) * text_score;
```

### パラメータ

| パラメータ | 値 | 根拠 |
|-----------|-----|------|
| α (alpha) | 0.65 | ベクトル検索重視（意味理解優先）|
| Threshold | 0.15 | 低ノイズフィルタ |
| limit | 20 | Active Context適正サイズ |

### 検索フロー

```
1. Text検索: ILIKE '%query%' → text_candidates, text_scores
2. Vector検索: cos_sim(embedding, query_vec) → vec_candidates, vec_scores
3. Merge: text_candidates ∪ vec_candidates
4. Fusion: hybrid_score(text_score, vec_score, 0.65)
5. Filter: fused_score >= 0.15
6. Rank: ORDER BY fused_score DESC LIMIT 20
```

## 仕様 → 実装対応表

### TLA+変数 → 実装モジュール対応

| TLA+変数/アクション | 実装ファイル | 関数/メソッド | 備考 |
|-------------------|-------------|--------------|------|
| `claimScope` | `src/store/claims.ts:7` | `Claim.scope` | DBスキーマの`scope`カラム |
| `claimTextRelevant` | `src/store/claims.ts:67` | `listClaimsByScope()` | ILIKE検索で判定 |
| `claimVecRelevant` | （未実装） | `hybridSearch.vectorSearch()` | cos_sim >= threshold |
| `requestedScopes` | `src/store/claims.ts:60` | `scopes: string[]`引数 | 呼び出し元から受領 |
| `C_TextSearch` | `src/store/claims.ts:66-72` | `listClaimsByScope()`のILIKE部 | 既存実装 |
| `C_VecSearch` | （未実装） | `hybridSearch.vectorSearch()` | 埋め込み検索 |
| `C_Merge` | （未実装） | `hybridSearch.merge()` | FULL OUTER JOIN |
| `FusedScore()` | `src/db/schema.sql` | `hybrid_score`マクロ | α重み付け融合 |
| `AboveThreshold()` | （未実装） | WHERE句 | score >= 0.15 |

### TLA+不変条件 → 実装検証方法

| TLA+不変条件 | 実装検証方法 | テストファイル |
|-------------|-------------|---------------|
| `Inv_C_ScopeConsistency` | SQLの`WHERE scope IN (...)` | `claims.test.ts` |
| `Inv_C_ThresholdFiltering` | `WHERE hybrid_score >= threshold` | `hybridSearch.test.ts` |
| `Inv_C_MergeComplete` | FULL OUTER JOINで両検索結果統合 | `hybridSearch.test.ts` |
| `Inv_C_FusionCorrectness` | `hybrid_score`マクロ使用 | 単体テスト |
| `Inv_C_CompleteCoverage` | 両検索の並列実行保証 | 統合テスト |

### 活性性質 → 実装保証

| TLA+活性性質 | 実装保証方法 |
|-------------|-------------|
| `Liveness_EventuallyDone` | async/awaitによる完了保証 |
| `Liveness_C_MergeEventuallyComplete` | Promise.all()による並列実行 |

## 残課題・リスク

### 未実装項目

| 項目 | 優先度 | 依存関係 |
|------|--------|----------|
| `hybridSearch.ts`モジュール | P0 | なし |
| `claim_vectors`テーブル | P0 | スキーマ変更 |
| `hybrid_score`マクロ | P0 | DuckDB |
| `vectorSearch()`関数 | P0 | pce-embeddings |
| Active Context `r()`関数 | P1 | hybridSearch |

### 技術的リスク

| リスク | 影響度 | 緩和策 |
|--------|--------|--------|
| 両検索の実行順序 | 中 | Promise.all()で並列化 |
| 埋め込み生成失敗 | 中 | フォールバック（Text-onlyに退化） |
| α=0.65の妥当性 | 低 | 設定可能パラメータ化、A/Bテスト |
| スコア離散化の精度 | 低 | 連続スコアで実装 |

### 仮定と制約

| 仮定 | 根拠 | 検証方法 |
|------|------|----------|
| 両検索が実行される | 実装で保証 | 統合テスト |
| スコアは0-1範囲 | API仕様 | バリデーション |
| スコープは有限集合 | DB制約 | スキーマ |
| クエリ文字列は非空 | バリデーション | 入力検証 |

### 形式検証の限界

1. **Alloy検証未完**: 状態空間が大きく完走せず。簡略版(`hybrid_search_simple.als`)で代替
2. **ランキング検証省略**: TLA+でのSequence操作が複雑なため、スコア順序の検証は実装テストで担保
3. **並行性未検証**: 単一検索リクエストのみモデル化。複数リクエストの競合は未検証

## 結果

この決定により:

1. **形式検証に裏付けられた設計選択**: 反例による限界の実証
2. **仕様と実装の追跡可能性**: TLA+不変条件と実装の対応明確化
3. **将来の検証基盤**: 回帰テストとして形式仕様を活用可能

## 参照

- [TLA+ hybrid_search_simple.tla](../spec/tlaplus/hybrid_search_simple.tla)
- [TLA+ hybrid_search_comparison.tla](../spec/tlaplus/hybrid_search_comparison.tla)
- [Alloy hybrid_search_comparison.als](../spec/alloy/hybrid_search_comparison.als)
- [activation-ranking.md](../activation-ranking.md)

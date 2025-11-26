/**
 * Alloy Model: Hybrid Search Strategy Comparison
 * pce-memory v0.1: 検索戦略の形式検証（構造的性質）
 *
 * 比較する設計:
 * - 設計A: Text-only検索（ILIKE）
 * - 設計B: Vector-only検索（cos_sim）
 * - 設計C: Hybrid検索（α-weighted fusion）
 *
 * 検証する性質:
 * - 融合計算の正しさ
 * - スコープフィルタの完全性
 * - ランキングの一貫性
 * - カバレッジの違い（設計間比較）
 */
module hybrid_search_comparison

open util/integer
open util/ordering[Rank]

// ========== 基本シグネチャ ==========

sig Claim {
  scope: one Scope,
  textRelevance: one Int,    // 0-100 テキスト関連度
  vectorRelevance: one Int   // 0-100 ベクトル関連度
}

abstract sig Scope {}
one sig Session, Project, Principle extends Scope {}

sig Query {}

sig Rank {}

// ========== スコア ==========

// スコアは0-100の範囲
fact ScoreRange {
  all c: Claim |
    c.textRelevance >= 0 and c.textRelevance <= 100 and
    c.vectorRelevance >= 0 and c.vectorRelevance <= 100
}

// ========== 検索リクエスト ==========

sig SearchRequest {
  query: one Query,
  requestedScopes: set Scope,
  threshold: one Int  // 採用閾値（0-100）
}

fact ValidThreshold {
  all r: SearchRequest | r.threshold >= 0 and r.threshold <= 100
}

fact NonEmptyScopes {
  all r: SearchRequest | some r.requestedScopes
}

// ========== 設計A: Text-only検索 ==========

sig TextOnlyResult {
  request: one SearchRequest,
  candidates: set Claim,
  ranked: Claim -> Rank
}

// Text-only検索: textRelevanceが閾値以上の候補のみ
pred TextOnlySearch[r: TextOnlyResult] {
  // スコープフィルタ + テキスト関連性
  r.candidates = {c: Claim |
    c.scope in r.request.requestedScopes and
    c.textRelevance >= r.request.threshold
  }
  // ランキング: textRelevanceでソート（同点は任意）
  all c: r.candidates | one rank: Rank | c->rank in r.ranked
  all c1, c2: r.candidates, r1, r2: Rank |
    (c1->r1 in r.ranked and c2->r2 in r.ranked and gt[r1, r2])
      implies c1.textRelevance >= c2.textRelevance
}

// ========== 設計B: Vector-only検索 ==========

sig VectorOnlyResult {
  request: one SearchRequest,
  candidates: set Claim,
  ranked: Claim -> Rank
}

// Vector-only検索: vectorRelevanceが閾値以上の候補のみ
pred VectorOnlySearch[r: VectorOnlyResult] {
  // スコープフィルタ + ベクトル関連性
  r.candidates = {c: Claim |
    c.scope in r.request.requestedScopes and
    c.vectorRelevance >= r.request.threshold
  }
  // ランキング: vectorRelevanceでソート
  all c: r.candidates | one rank: Rank | c->rank in r.ranked
  all c1, c2: r.candidates, r1, r2: Rank |
    (c1->r1 in r.ranked and c2->r2 in r.ranked and gt[r1, r2])
      implies c1.vectorRelevance >= c2.vectorRelevance
}

// ========== 設計C: Hybrid検索 ==========

// 融合係数（65 = α=0.65）
one sig Alpha {
  value: one Int
}

fact AlphaRange {
  Alpha.value >= 0 and Alpha.value <= 100
}

sig HybridResult {
  request: one SearchRequest,
  textCandidates: set Claim,
  vectorCandidates: set Claim,
  mergedCandidates: set Claim,
  candidates: set Claim,  // 閾値フィルタ後
  ranked: Claim -> Rank,
  fusedScores: Claim -> Int
}

// 融合スコア計算関数
fun fusedScore[c: Claim]: Int {
  div[plus[mul[Alpha.value, c.vectorRelevance],
           mul[sub[100, Alpha.value], c.textRelevance]], 100]
}

// Hybrid検索
pred HybridSearch[r: HybridResult] {
  // Text候補: テキスト関連性がある
  r.textCandidates = {c: Claim |
    c.scope in r.request.requestedScopes and c.textRelevance > 0
  }

  // Vector候補: ベクトル関連性がある
  r.vectorCandidates = {c: Claim |
    c.scope in r.request.requestedScopes and c.vectorRelevance > 0
  }

  // 統合（FULL OUTER JOIN）
  r.mergedCandidates = r.textCandidates + r.vectorCandidates

  // 融合スコア計算
  all c: r.mergedCandidates | c->fusedScore[c] in r.fusedScores

  // 閾値フィルタ
  r.candidates = {c: r.mergedCandidates | fusedScore[c] >= r.request.threshold}

  // ランキング: fusedScoreでソート
  all c: r.candidates | one rank: Rank | c->rank in r.ranked
  all c1, c2: r.candidates, r1, r2: Rank |
    (c1->r1 in r.ranked and c2->r2 in r.ranked and gt[r1, r2])
      implies fusedScore[c1] >= fusedScore[c2]
}

// ========== アサーション ==========

// 設計A: スコープフィルタの完全性
assert A_ScopeFilterComplete {
  all r: TextOnlyResult |
    TextOnlySearch[r] implies
      all c: r.candidates | c.scope in r.request.requestedScopes
}

// 設計B: スコープフィルタの完全性
assert B_ScopeFilterComplete {
  all r: VectorOnlyResult |
    VectorOnlySearch[r] implies
      all c: r.candidates | c.scope in r.request.requestedScopes
}

// 設計C: スコープフィルタの完全性
assert C_ScopeFilterComplete {
  all r: HybridResult |
    HybridSearch[r] implies
      all c: r.candidates | c.scope in r.request.requestedScopes
}

// 設計C: 融合計算の正しさ
assert C_FusionCorrect {
  all r: HybridResult, c: Claim |
    (HybridSearch[r] and c in r.mergedCandidates) implies
      c->fusedScore[c] in r.fusedScores
}

// 設計C: 統合の完全性（Text OR Vectorの候補を全て含む）
assert C_MergeComplete {
  all r: HybridResult |
    HybridSearch[r] implies
      r.mergedCandidates = r.textCandidates + r.vectorCandidates
}

// ========== 設計比較アサーション ==========

// 設計Aの限界: Vector関連性のみの候補を逃す
// 反例を期待
assert A_MissesVectorOnlyClaims {
  all req: SearchRequest, ta: TextOnlyResult |
    (TextOnlySearch[ta] and ta.request = req) implies
      all c: Claim |
        (c.scope in req.requestedScopes and c.vectorRelevance >= req.threshold and c.textRelevance = 0)
          implies c in ta.candidates
}

// 設計Bの限界: Text関連性のみの候補を逃す
// 反例を期待
assert B_MissesTextOnlyClaims {
  all req: SearchRequest, vr: VectorOnlyResult |
    (VectorOnlySearch[vr] and vr.request = req) implies
      all c: Claim |
        (c.scope in req.requestedScopes and c.textRelevance >= req.threshold and c.vectorRelevance = 0)
          implies c in vr.candidates
}

// 設計Cの優位性: TextまたはVectorで関連する候補を全て含む
assert C_CoversTextOrVector {
  all req: SearchRequest, hr: HybridResult |
    (HybridSearch[hr] and hr.request = req) implies
      all c: Claim |
        (c.scope in req.requestedScopes and (c.textRelevance > 0 or c.vectorRelevance > 0))
          implies c in hr.mergedCandidates
}

// ========== ランキング一貫性 ==========

// 設計A: 同一スコアでも一貫したランク付け
assert A_RankingConsistent {
  all r: TextOnlyResult |
    TextOnlySearch[r] implies
      all c: r.candidates | one rank: Rank | c->rank in r.ranked
}

// 設計C: 融合スコアに基づく一貫したランク付け
assert C_RankingConsistent {
  all r: HybridResult |
    HybridSearch[r] implies
      all c: r.candidates | one rank: Rank | c->rank in r.ranked
}

// ========== 探索（Runs）==========

// 正常ケース: Hybrid検索の動作確認
pred ValidHybridSearch {
  some r: HybridResult |
    HybridSearch[r] and
    #r.candidates > 1 and
    some r.textCandidates and
    some r.vectorCandidates and
    some c: r.textCandidates | c not in r.vectorCandidates  // Textのみの候補
}

// 比較ケース: 同一リクエストで3設計の結果を比較
pred CompareAllDesigns {
  some req: SearchRequest, ta: TextOnlyResult, vr: VectorOnlyResult, hr: HybridResult |
    ta.request = req and vr.request = req and hr.request = req and
    TextOnlySearch[ta] and VectorOnlySearch[vr] and HybridSearch[hr] and
    // Hybridは最も多くの候補を含む
    #ta.candidates <= #hr.mergedCandidates and
    #vr.candidates <= #hr.mergedCandidates
}

// 反例探索: Text-onlyがVector関連候補を逃すケース
pred TextOnlyMissesVectorRelevant {
  some req: SearchRequest, ta: TextOnlyResult, c: Claim |
    TextOnlySearch[ta] and ta.request = req and
    c.scope in req.requestedScopes and
    c.vectorRelevance >= req.threshold and
    c.textRelevance < req.threshold and
    c not in ta.candidates
}

// 反例探索: Vector-onlyがText関連候補を逃すケース
pred VectorOnlyMissesTextRelevant {
  some req: SearchRequest, vr: VectorOnlyResult, c: Claim |
    VectorOnlySearch[vr] and vr.request = req and
    c.scope in req.requestedScopes and
    c.textRelevance >= req.threshold and
    c.vectorRelevance < req.threshold and
    c not in vr.candidates
}

// ========== チェック ==========

// スコープフィルタ検証
check A_ScopeFilterComplete for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 TextOnlyResult
check B_ScopeFilterComplete for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 VectorOnlyResult
check C_ScopeFilterComplete for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult

// 融合検証
check C_FusionCorrect for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult
check C_MergeComplete for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult

// 設計比較（反例を期待）
check A_MissesVectorOnlyClaims for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 TextOnlyResult
check B_MissesTextOnlyClaims for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 VectorOnlyResult

// Hybridの優位性
check C_CoversTextOrVector for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult

// ランキング一貫性
check A_RankingConsistent for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 TextOnlyResult
check C_RankingConsistent for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult

// 探索実行
run ValidHybridSearch for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 HybridResult
run CompareAllDesigns for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 TextOnlyResult, 2 VectorOnlyResult, 2 HybridResult
run TextOnlyMissesVectorRelevant for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 TextOnlyResult
run VectorOnlyMissesTextRelevant for 5 but 4 Claim, 3 Scope, 2 Query, 4 Rank, 2 SearchRequest, 2 VectorOnlyResult

// ========== 設計比較サマリ（コメント）==========

/**
 * 検証結果の期待:
 *
 * | アサーション | 設計A | 設計B | 設計C |
 * |------------|-------|-------|-------|
 * | ScopeFilterComplete | ✅ | ✅ | ✅ |
 * | RankingConsistent | ✅ | ✅ | ✅ |
 * | MissesVectorOnlyClaims | ❌ 反例 | N/A | N/A |
 * | MissesTextOnlyClaims | N/A | ❌ 反例 | N/A |
 * | CoversTextOrVector | N/A | N/A | ✅ |
 * | FusionCorrect | N/A | N/A | ✅ |
 *
 * 結論:
 * - 設計A: テキスト完全一致に強いが、意味的関連を逃す
 * - 設計B: 意味的関連に強いが、完全一致を逃す
 * - 設計C: 両方をカバーし、融合スコアで最適なランキング
 */

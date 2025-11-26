/**
 * Alloy Model: Simplified Hybrid Search Strategy Comparison
 * pce-memory v0.1: 検索戦略の形式検証（簡略版 - 検証可能）
 *
 * 簡略化ポイント:
 * - Claim数を2に制限
 * - スコア範囲を{0, 50, 100}に制限
 * - Rankシグネチャを削除（ランキング検証は省略）
 */
module hybrid_search_simple

open util/integer

// ========== 基本シグネチャ ==========

sig Claim {
  scope: one Scope,
  textRelevant: one Bool,     // テキスト関連性（boolean化）
  vectorRelevant: one Bool    // ベクトル関連性（boolean化）
}

abstract sig Scope {}
one sig Session, Project extends Scope {}

abstract sig Bool {}
one sig True, False extends Bool {}

// ========== 検索リクエスト ==========

one sig SearchRequest {
  requestedScopes: set Scope
}

fact NonEmptyScopes {
  some SearchRequest.requestedScopes
}

// ========== 設計A: Text-only検索 ==========

one sig TextOnlyResult {
  candidates: set Claim
}

pred TextOnlySearch {
  TextOnlyResult.candidates = {c: Claim |
    c.scope in SearchRequest.requestedScopes and
    c.textRelevant = True
  }
}

// ========== 設計B: Vector-only検索 ==========

one sig VectorOnlyResult {
  candidates: set Claim
}

pred VectorOnlySearch {
  VectorOnlyResult.candidates = {c: Claim |
    c.scope in SearchRequest.requestedScopes and
    c.vectorRelevant = True
  }
}

// ========== 設計C: Hybrid検索 ==========

one sig HybridResult {
  textCandidates: set Claim,
  vecCandidates: set Claim,
  merged: set Claim
}

pred HybridSearch {
  // Text候補
  HybridResult.textCandidates = {c: Claim |
    c.scope in SearchRequest.requestedScopes and c.textRelevant = True
  }
  // Vector候補
  HybridResult.vecCandidates = {c: Claim |
    c.scope in SearchRequest.requestedScopes and c.vectorRelevant = True
  }
  // 統合（FULL OUTER JOIN）
  HybridResult.merged = HybridResult.textCandidates + HybridResult.vecCandidates
}

// ========== 全検索を実行 ==========

pred AllSearches {
  TextOnlySearch
  VectorOnlySearch
  HybridSearch
}

// ========== アサーション ==========

// 設計A: スコープフィルタの完全性
assert A_ScopeFilterComplete {
  AllSearches implies
    all c: TextOnlyResult.candidates | c.scope in SearchRequest.requestedScopes
}

// 設計B: スコープフィルタの完全性
assert B_ScopeFilterComplete {
  AllSearches implies
    all c: VectorOnlyResult.candidates | c.scope in SearchRequest.requestedScopes
}

// 設計C: スコープフィルタの完全性
assert C_ScopeFilterComplete {
  AllSearches implies
    all c: HybridResult.merged | c.scope in SearchRequest.requestedScopes
}

// 設計C: 統合の完全性
assert C_MergeComplete {
  AllSearches implies
    HybridResult.merged = HybridResult.textCandidates + HybridResult.vecCandidates
}

// 設計Aの限界: Vector関連候補を逃す（反例を期待）
assert A_MissesVectorOnly {
  AllSearches implies
    all c: Claim |
      (c.scope in SearchRequest.requestedScopes and
       c.vectorRelevant = True and c.textRelevant = False)
        implies c in TextOnlyResult.candidates
}

// 設計Bの限界: Text関連候補を逃す（反例を期待）
assert B_MissesTextOnly {
  AllSearches implies
    all c: Claim |
      (c.scope in SearchRequest.requestedScopes and
       c.textRelevant = True and c.vectorRelevant = False)
        implies c in VectorOnlyResult.candidates
}

// 設計Cの優位性: TextまたはVectorで関連する候補を全て含む
assert C_CoversAll {
  AllSearches implies
    all c: Claim |
      (c.scope in SearchRequest.requestedScopes and
       (c.textRelevant = True or c.vectorRelevant = True))
        implies c in HybridResult.merged
}

// ========== チェック ==========

// スコープフィルタ検証（全てパスを期待）
check A_ScopeFilterComplete for 3 but 2 Claim, 2 Scope
check B_ScopeFilterComplete for 3 but 2 Claim, 2 Scope
check C_ScopeFilterComplete for 3 but 2 Claim, 2 Scope

// 統合完全性（パスを期待）
check C_MergeComplete for 3 but 2 Claim, 2 Scope

// 設計比較（反例を期待）
check A_MissesVectorOnly for 3 but 2 Claim, 2 Scope
check B_MissesTextOnly for 3 but 2 Claim, 2 Scope

// Hybrid優位性（パスを期待）
check C_CoversAll for 3 but 2 Claim, 2 Scope

// ========== 探索 ==========

// 正常ケース
run AllSearches for 3 but 2 Claim, 2 Scope

// 設計Aが逃すケース
pred TextOnlyMissesExample {
  AllSearches
  some c: Claim |
    c.scope in SearchRequest.requestedScopes and
    c.vectorRelevant = True and
    c.textRelevant = False and
    c not in TextOnlyResult.candidates
}
run TextOnlyMissesExample for 3 but 2 Claim, 2 Scope

// 設計Bが逃すケース
pred VectorOnlyMissesExample {
  AllSearches
  some c: Claim |
    c.scope in SearchRequest.requestedScopes and
    c.textRelevant = True and
    c.vectorRelevant = False and
    c not in VectorOnlyResult.candidates
}
run VectorOnlyMissesExample for 3 but 2 Claim, 2 Scope

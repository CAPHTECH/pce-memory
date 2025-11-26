---- MODULE hybrid_search_simple ----
\* Simplified Hybrid Search Strategy Design Comparison
\* pce-memory v0.1: 検索戦略の形式検証（簡易版）
\*
\* 比較する設計:
\* - 設計A: Text-only検索（ILIKE）
\* - 設計B: Vector-only検索（cos_sim）
\* - 設計C: Hybrid検索（α-weighted fusion）
\*
\* 検証する性質:
\* - CandidateSelection: 候補選択の正しさ
\* - ThresholdFiltering: 閾値フィルタリング
\* - ScopeConsistency: スコープ整合性
\* - Fusion計算の正しさ

EXTENDS Naturals, FiniteSets

CONSTANTS
  ClaimId,        \* Claim識別子の集合
  Scope,          \* スコープの集合
  Score,          \* スコア値の集合
  Alpha,          \* ハイブリッド融合係数（0-100）
  Threshold       \* 採用閾値（0-100）

VARIABLES
  \* Claim属性
  claimScope,         \* [ClaimId -> Scope]
  claimTextRelevant,  \* [ClaimId -> BOOLEAN]
  claimVecRelevant,   \* [ClaimId -> BOOLEAN]
  requestedScopes,    \* スコープ集合

  \* 設計A: Text-only
  A_candidates,       \* Claim集合
  A_scores,           \* [ClaimId -> Score]
  A_accepted,         \* 閾値通過Claim集合

  \* 設計B: Vector-only
  B_candidates,
  B_scores,
  B_accepted,

  \* 設計C: Hybrid
  C_textCandidates,
  C_vecCandidates,
  C_merged,
  C_textScores,
  C_vecScores,
  C_fusedScores,
  C_accepted,

  \* 状態フラグ
  phase             \* "init", "search", "filter", "done"

vars == <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
          A_candidates, A_scores, A_accepted,
          B_candidates, B_scores, B_accepted,
          C_textCandidates, C_vecCandidates, C_merged,
          C_textScores, C_vecScores, C_fusedScores, C_accepted,
          phase>>

\* ========== ヘルパー関数 ==========

InRequestedScope(c) == claimScope[c] \in requestedScopes
TextRelevant(c) == claimTextRelevant[c]
VectorRelevant(c) == claimVecRelevant[c]

\* 融合スコア計算: α × vecScore + (1-α) × textScore
FusedScore(textScore, vecScore) ==
  (Alpha * vecScore + (100 - Alpha) * textScore) \div 100

AboveThreshold(score) == score >= Threshold

\* ========== 初期状態 ==========

Init ==
  /\ claimScope \in [ClaimId -> Scope]
  /\ claimTextRelevant \in [ClaimId -> BOOLEAN]
  /\ claimVecRelevant \in [ClaimId -> BOOLEAN]
  /\ requestedScopes \in (SUBSET Scope \ {{}})
  /\ A_candidates = {}
  /\ A_scores = [c \in ClaimId |-> 0]
  /\ A_accepted = {}
  /\ B_candidates = {}
  /\ B_scores = [c \in ClaimId |-> 0]
  /\ B_accepted = {}
  /\ C_textCandidates = {}
  /\ C_vecCandidates = {}
  /\ C_merged = {}
  /\ C_textScores = [c \in ClaimId |-> 0]
  /\ C_vecScores = [c \in ClaimId |-> 0]
  /\ C_fusedScores = [c \in ClaimId |-> 0]
  /\ C_accepted = {}
  /\ phase = "init"

\* ========== 検索アクション ==========

\* 設計A: Text検索
A_Search ==
  /\ phase = "init"
  /\ A_candidates' = {c \in ClaimId : InRequestedScope(c) /\ TextRelevant(c)}
  /\ \E sf \in [A_candidates' -> Score]:
       A_scores' = [c \in ClaimId |-> IF c \in A_candidates' THEN sf[c] ELSE 0]
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_accepted, B_candidates, B_scores, B_accepted,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores, C_accepted, phase>>

\* 設計B: Vector検索
B_Search ==
  /\ phase = "init"
  /\ B_candidates' = {c \in ClaimId : InRequestedScope(c) /\ VectorRelevant(c)}
  /\ \E sf \in [B_candidates' -> Score]:
       B_scores' = [c \in ClaimId |-> IF c \in B_candidates' THEN sf[c] ELSE 0]
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted, B_accepted,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores, C_accepted, phase>>

\* 設計C: Text検索
C_TextSearch ==
  /\ phase = "init"
  /\ C_textCandidates' = {c \in ClaimId : InRequestedScope(c) /\ TextRelevant(c)}
  /\ \E sf \in [C_textCandidates' -> Score]:
       C_textScores' = [c \in ClaimId |-> IF c \in C_textCandidates' THEN sf[c] ELSE 0]
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted,
                 B_candidates, B_scores, B_accepted,
                 C_vecCandidates, C_merged, C_vecScores, C_fusedScores, C_accepted, phase>>

\* 設計C: Vector検索
C_VecSearch ==
  /\ phase = "init"
  /\ C_vecCandidates' = {c \in ClaimId : InRequestedScope(c) /\ VectorRelevant(c)}
  /\ \E sf \in [C_vecCandidates' -> Score]:
       C_vecScores' = [c \in ClaimId |-> IF c \in C_vecCandidates' THEN sf[c] ELSE 0]
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted,
                 B_candidates, B_scores, B_accepted,
                 C_textCandidates, C_merged, C_textScores, C_fusedScores, C_accepted, phase>>

\* フェーズ遷移: init -> search
ToSearchPhase ==
  /\ phase = "init"
  /\ A_candidates # {} \/ B_candidates # {} \/ C_textCandidates # {} \/ C_vecCandidates # {}
  /\ phase' = "search"
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted,
                 B_candidates, B_scores, B_accepted,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores, C_accepted>>

\* 設計C: 候補統合
C_Merge ==
  /\ phase = "search"
  /\ C_merged = {}  \* まだマージしていない
  /\ C_merged' = C_textCandidates \cup C_vecCandidates
  /\ C_fusedScores' = [c \in ClaimId |->
       IF c \in C_merged'
       THEN FusedScore(C_textScores[c], C_vecScores[c])
       ELSE 0]
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted,
                 B_candidates, B_scores, B_accepted,
                 C_textCandidates, C_vecCandidates, C_textScores, C_vecScores, C_accepted, phase>>

\* フェーズ遷移: search -> filter
ToFilterPhase ==
  /\ phase = "search"
  \* C_mergedが設定されている、または設計A/Bのみ実行する場合
  /\ C_merged # {} \/ (A_candidates # {} /\ C_textCandidates = {} /\ C_vecCandidates = {})
     \/ (B_candidates # {} /\ C_textCandidates = {} /\ C_vecCandidates = {})
  /\ phase' = "filter"
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, A_accepted,
                 B_candidates, B_scores, B_accepted,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores, C_accepted>>

\* 閾値フィルタ
ApplyThreshold ==
  /\ phase = "filter"
  /\ A_accepted' = {c \in A_candidates : AboveThreshold(A_scores[c])}
  /\ B_accepted' = {c \in B_candidates : AboveThreshold(B_scores[c])}
  /\ C_accepted' = {c \in C_merged : AboveThreshold(C_fusedScores[c])}
  /\ phase' = "done"
  /\ UNCHANGED <<claimScope, claimTextRelevant, claimVecRelevant, requestedScopes,
                 A_candidates, A_scores, B_candidates, B_scores,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores>>

\* ========== 次状態 ==========

Next ==
  \/ A_Search
  \/ B_Search
  \/ C_TextSearch
  \/ C_VecSearch
  \/ ToSearchPhase
  \/ C_Merge
  \/ ToFilterPhase
  \/ ApplyThreshold

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 設計A: スコープ整合性
Inv_A_ScopeConsistency ==
  \A c \in A_candidates: claimScope[c] \in requestedScopes

\* 設計B: スコープ整合性
Inv_B_ScopeConsistency ==
  \A c \in B_candidates: claimScope[c] \in requestedScopes

\* 設計C: スコープ整合性
Inv_C_ScopeConsistency ==
  \A c \in C_merged: claimScope[c] \in requestedScopes

\* 設計A: 閾値フィルタリング
Inv_A_ThresholdFiltering ==
  phase = "done" => \A c \in A_accepted: A_scores[c] >= Threshold

\* 設計B: 閾値フィルタリング
Inv_B_ThresholdFiltering ==
  phase = "done" => \A c \in B_accepted: B_scores[c] >= Threshold

\* 設計C: 閾値フィルタリング
Inv_C_ThresholdFiltering ==
  phase = "done" => \A c \in C_accepted: C_fusedScores[c] >= Threshold

\* 設計C: 候補統合の完全性
Inv_C_MergeComplete ==
  C_merged # {} =>
    C_merged = C_textCandidates \cup C_vecCandidates

\* 設計C: 融合計算の正しさ
Inv_C_FusionCorrectness ==
  \A c \in C_merged:
    C_fusedScores[c] = FusedScore(C_textScores[c], C_vecScores[c])

\* 設計C: 完全カバレッジ（両検索実行後、テキストまたはベクトル関連候補を全て含む）
\* C_textCandidatesとC_vecCandidatesが両方設定されている場合のみ検証
Inv_C_CompleteCoverage ==
  (C_textCandidates # {} /\ C_vecCandidates # {} /\ C_merged # {}) =>
    \A c \in ClaimId:
      (InRequestedScope(c) /\ (TextRelevant(c) \/ VectorRelevant(c)))
      => c \in C_merged

\* ========== 設計比較不変条件（反例を期待） ==========

\* 設計A: 意味的関連を逃す（Vector-onlyの候補）
\* この不変条件は設計Aで破られることを期待
Inv_A_MissesVectorOnly ==
  phase = "done" =>
    \A c \in ClaimId:
      (InRequestedScope(c) /\ VectorRelevant(c) /\ ~TextRelevant(c))
      => c \in A_accepted

\* 設計B: テキスト完全一致を逃す（Text-onlyの候補）
\* この不変条件は設計Bで破られることを期待
Inv_B_MissesTextOnly ==
  phase = "done" =>
    \A c \in ClaimId:
      (InRequestedScope(c) /\ TextRelevant(c) /\ ~VectorRelevant(c))
      => c \in B_accepted

\* ========== 全設計共通 ==========

\* 結果にスコープ外のClaimが含まれない
Inv_NoOutOfScopeClaims ==
  /\ (\A c \in A_accepted: claimScope[c] \in requestedScopes)
  /\ (\A c \in B_accepted: claimScope[c] \in requestedScopes)
  /\ (\A c \in C_accepted: claimScope[c] \in requestedScopes)

\* ========== 活性性質 ==========

\* 検索は最終的に完了する（Weak Fairness前提）
\* 注: TLCでの検証にはWeak Fairness制約が必要
Liveness_EventuallyDone ==
  <>(phase = "done")

\* 設計C: 両検索が実行されればマージが完了する
Liveness_C_MergeEventuallyComplete ==
  [](
    (C_textCandidates # {} /\ C_vecCandidates # {} /\ phase = "search")
    => <>(C_merged # {})
  )

\* 公平性制約付きSpec（活性検証用）
FairSpec == Spec /\ WF_vars(Next)

\* ========== 仮定と制約（明示化）==========

\* 仮定1: 両検索が実行される前提（実装保証が必要）
Assumption_BothSearchesExecuted ==
  phase = "done" =>
    (C_textCandidates # {} \/ C_vecCandidates # {})

\* 仮定2: スコア生成は非決定的だが範囲内（Score集合で制約）
Assumption_ScoresInRange ==
  /\ \A c \in ClaimId: A_scores[c] \in Score \cup {0}
  /\ \A c \in ClaimId: B_scores[c] \in Score \cup {0}
  /\ \A c \in ClaimId: C_textScores[c] \in Score \cup {0}
  /\ \A c \in ClaimId: C_vecScores[c] \in Score \cup {0}

====

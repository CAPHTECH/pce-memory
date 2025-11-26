---- MODULE hybrid_search_comparison ----
\* Hybrid Search Strategy Design Comparison
\* pce-memory v0.1: 検索戦略の形式検証
\*
\* 比較する設計:
\* - 設計A: Text-only検索（ILIKE）
\* - 設計B: Vector-only検索（cos_sim）
\* - 設計C: Hybrid検索（α-weighted fusion）
\*
\* 検証する性質:
\* - RankingCorrectness: スコアの高い候補が先にランクされる
\* - ThresholdFiltering: 閾値未満の候補は除外される
\* - ScopeConsistency: 全結果がスコープフィルタを満たす
\* - SemanticCoverage: 意味的に関連する候補が取得される
\* - ExactMatchCoverage: 完全一致候補が取得される

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  ClaimId,        \* Claim識別子の集合
  Scope,          \* スコープの集合 {session, project, principle}
  Query,          \* クエリの集合
  Score,          \* スコア値の集合（0-100の整数で近似）
  Alpha,          \* ハイブリッド融合係数（0-100、65=0.65）
  Threshold       \* 採用閾値（0-100）

VARIABLES
  \* 共通状態
  claims,             \* [ClaimId -> [text: TEXT, scope: Scope, textRelevant: BOOLEAN, vectorRelevant: BOOLEAN]]
  currentQuery,       \* 現在のクエリ
  requestedScopes,    \* リクエストされたスコープ集合

  \* 設計A: Text-only検索
  A_candidates,       \* Text検索による候補集合
  A_results,          \* 最終結果（ランク付き）
  A_scores,           \* [ClaimId -> Score]

  \* 設計B: Vector-only検索
  B_candidates,       \* Vector検索による候補集合
  B_results,          \* 最終結果（ランク付き）
  B_scores,           \* [ClaimId -> Score]

  \* 設計C: Hybrid検索
  C_textCandidates,   \* Text検索による候補
  C_vecCandidates,    \* Vector検索による候補
  C_merged,           \* 統合後の候補
  C_results,          \* 最終結果（ランク付き）
  C_textScores,       \* [ClaimId -> Score]
  C_vecScores,        \* [ClaimId -> Score]
  C_fusedScores       \* [ClaimId -> Score]

vars == <<claims, currentQuery, requestedScopes,
          A_candidates, A_results, A_scores,
          B_candidates, B_results, B_scores,
          C_textCandidates, C_vecCandidates, C_merged, C_results,
          C_textScores, C_vecScores, C_fusedScores>>

\* ========== 型定義 ==========

\* Claimの属性（TLC検証可能な形式）
ClaimRec == [scope: Scope, textRelevant: BOOLEAN, vectorRelevant: BOOLEAN]
ResultRec == [claimId: ClaimId, score: Score, rank: Nat]

\* ========== ヘルパー関数 ==========

\* スコープフィルタを満たすか
InRequestedScope(cid) == claims[cid].scope \in requestedScopes

\* Text関連性（ILIKE相当）
TextRelevant(cid) == claims[cid].textRelevant

\* Vector関連性（cos_sim相当）
VectorRelevant(cid) == claims[cid].vectorRelevant

\* 融合スコア計算: α × vecScore + (1-α) × textScore
\* Alpha, スコアは0-100の整数で近似
FusedScore(textScore, vecScore) ==
  (Alpha * vecScore + (100 - Alpha) * textScore) \div 100

\* 閾値以上か
AboveThreshold(score) == score >= Threshold

\* シーケンスがスコア降順か
IsDescendingByScore(seq) ==
  \A i \in 1..(Len(seq)-1): seq[i].score >= seq[i+1].score

\* ========== 初期状態 ==========

Init ==
  /\ claims \in [ClaimId -> ClaimRec]
  /\ currentQuery \in Query
  /\ requestedScopes \in SUBSET Scope
  /\ requestedScopes # {}
  \* 設計A初期化
  /\ A_candidates = {}
  /\ A_results = << >>
  /\ A_scores = [c \in ClaimId |-> 0]
  \* 設計B初期化
  /\ B_candidates = {}
  /\ B_results = << >>
  /\ B_scores = [c \in ClaimId |-> 0]
  \* 設計C初期化
  /\ C_textCandidates = {}
  /\ C_vecCandidates = {}
  /\ C_merged = {}
  /\ C_results = << >>
  /\ C_textScores = [c \in ClaimId |-> 0]
  /\ C_vecScores = [c \in ClaimId |-> 0]
  /\ C_fusedScores = [c \in ClaimId |-> 0]

\* ========== 設計A: Text-only検索 ==========

\* Text検索実行
A_TextSearch ==
  /\ A_candidates = {}
  /\ A_candidates' = {c \in ClaimId : InRequestedScope(c) /\ TextRelevant(c)}
  /\ \E scoreFunc \in [A_candidates' -> Score]:
       A_scores' = [c \in ClaimId |-> IF c \in A_candidates' THEN scoreFunc[c] ELSE 0]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes, A_results,
                 B_candidates, B_results, B_scores,
                 C_textCandidates, C_vecCandidates, C_merged, C_results,
                 C_textScores, C_vecScores, C_fusedScores>>

\* 閾値フィルタと結果構築
A_BuildResults ==
  /\ A_candidates # {}
  /\ A_results = << >>
  /\ LET filtered == {c \in A_candidates : AboveThreshold(A_scores[c])}
         sorted == CHOOSE seq \in Seq(filtered) :
                     /\ \A c \in filtered : \E i \in 1..Len(seq) : seq[i] = c
                     /\ IsDescendingByScore([i \in 1..Len(seq) |-> [claimId |-> seq[i], score |-> A_scores[seq[i]], rank |-> i]])
     IN A_results' = [i \in 1..Len(sorted) |-> [claimId |-> sorted[i], score |-> A_scores[sorted[i]], rank |-> i]]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes, A_candidates, A_scores,
                 B_candidates, B_results, B_scores,
                 C_textCandidates, C_vecCandidates, C_merged, C_results,
                 C_textScores, C_vecScores, C_fusedScores>>

\* ========== 設計B: Vector-only検索 ==========

\* Vector検索実行
B_VectorSearch ==
  /\ B_candidates = {}
  /\ B_candidates' = {c \in ClaimId : InRequestedScope(c) /\ VectorRelevant(c)}
  /\ \E scoreFunc \in [B_candidates' -> Score]:
       B_scores' = [c \in ClaimId |-> IF c \in B_candidates' THEN scoreFunc[c] ELSE 0]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes, B_results,
                 A_candidates, A_results, A_scores,
                 C_textCandidates, C_vecCandidates, C_merged, C_results,
                 C_textScores, C_vecScores, C_fusedScores>>

\* 閾値フィルタと結果構築
B_BuildResults ==
  /\ B_candidates # {}
  /\ B_results = << >>
  /\ LET filtered == {c \in B_candidates : AboveThreshold(B_scores[c])}
         sorted == CHOOSE seq \in Seq(filtered) :
                     /\ \A c \in filtered : \E i \in 1..Len(seq) : seq[i] = c
                     /\ IsDescendingByScore([i \in 1..Len(seq) |-> [claimId |-> seq[i], score |-> B_scores[seq[i]], rank |-> i]])
     IN B_results' = [i \in 1..Len(sorted) |-> [claimId |-> sorted[i], score |-> B_scores[sorted[i]], rank |-> i]]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes, B_candidates, B_scores,
                 A_candidates, A_results, A_scores,
                 C_textCandidates, C_vecCandidates, C_merged, C_results,
                 C_textScores, C_vecScores, C_fusedScores>>

\* ========== 設計C: Hybrid検索 ==========

\* Text検索実行
C_TextSearch ==
  /\ C_textCandidates = {}
  /\ C_textCandidates' = {c \in ClaimId : InRequestedScope(c) /\ TextRelevant(c)}
  /\ \E scoreFunc \in [C_textCandidates' -> Score]:
       C_textScores' = [c \in ClaimId |-> IF c \in C_textCandidates' THEN scoreFunc[c] ELSE 0]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes,
                 A_candidates, A_results, A_scores,
                 B_candidates, B_results, B_scores,
                 C_vecCandidates, C_merged, C_results, C_vecScores, C_fusedScores>>

\* Vector検索実行
C_VectorSearch ==
  /\ C_vecCandidates = {}
  /\ C_vecCandidates' = {c \in ClaimId : InRequestedScope(c) /\ VectorRelevant(c)}
  /\ \E scoreFunc \in [C_vecCandidates' -> Score]:
       C_vecScores' = [c \in ClaimId |-> IF c \in C_vecCandidates' THEN scoreFunc[c] ELSE 0]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes,
                 A_candidates, A_results, A_scores,
                 B_candidates, B_results, B_scores,
                 C_textCandidates, C_merged, C_results, C_textScores, C_fusedScores>>

\* 候補統合（FULL OUTER JOIN相当）
C_MergeCandidates ==
  /\ C_textCandidates # {} \/ C_vecCandidates # {}
  /\ C_merged = {}
  /\ C_merged' = C_textCandidates \cup C_vecCandidates
  /\ C_fusedScores' = [c \in ClaimId |->
       IF c \in C_merged'
       THEN FusedScore(C_textScores[c], C_vecScores[c])
       ELSE 0]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes,
                 A_candidates, A_results, A_scores,
                 B_candidates, B_results, B_scores,
                 C_textCandidates, C_vecCandidates, C_results,
                 C_textScores, C_vecScores>>

\* 閾値フィルタと結果構築
C_BuildResults ==
  /\ C_merged # {}
  /\ C_results = << >>
  /\ LET filtered == {c \in C_merged : AboveThreshold(C_fusedScores[c])}
         sorted == CHOOSE seq \in Seq(filtered) :
                     /\ \A c \in filtered : \E i \in 1..Len(seq) : seq[i] = c
                     /\ IsDescendingByScore([i \in 1..Len(seq) |-> [claimId |-> seq[i], score |-> C_fusedScores[seq[i]], rank |-> i]])
     IN C_results' = [i \in 1..Len(sorted) |-> [claimId |-> sorted[i], score |-> C_fusedScores[sorted[i]], rank |-> i]]
  /\ UNCHANGED <<claims, currentQuery, requestedScopes,
                 A_candidates, A_results, A_scores,
                 B_candidates, B_results, B_scores,
                 C_textCandidates, C_vecCandidates, C_merged,
                 C_textScores, C_vecScores, C_fusedScores>>

\* ========== 次状態 ==========

Next ==
  \/ A_TextSearch
  \/ A_BuildResults
  \/ B_VectorSearch
  \/ B_BuildResults
  \/ C_TextSearch
  \/ C_VectorSearch
  \/ C_MergeCandidates
  \/ C_BuildResults

Spec == Init /\ [][Next]_vars

\* ========== 安全性不変条件 ==========

\* 設計A: ランキングの正しさ
Inv_A_RankingCorrectness ==
  IsDescendingByScore(A_results)

\* 設計A: 閾値フィルタリング
Inv_A_ThresholdFiltering ==
  \A i \in 1..Len(A_results): A_results[i].score >= Threshold

\* 設計A: スコープ整合性
Inv_A_ScopeConsistency ==
  \A i \in 1..Len(A_results): claims[A_results[i].claimId].scope \in requestedScopes

\* 設計B: ランキングの正しさ
Inv_B_RankingCorrectness ==
  IsDescendingByScore(B_results)

\* 設計B: 閾値フィルタリング
Inv_B_ThresholdFiltering ==
  \A i \in 1..Len(B_results): B_results[i].score >= Threshold

\* 設計B: スコープ整合性
Inv_B_ScopeConsistency ==
  \A i \in 1..Len(B_results): claims[B_results[i].claimId].scope \in requestedScopes

\* 設計C: ランキングの正しさ
Inv_C_RankingCorrectness ==
  IsDescendingByScore(C_results)

\* 設計C: 閾値フィルタリング
Inv_C_ThresholdFiltering ==
  \A i \in 1..Len(C_results): C_results[i].score >= Threshold

\* 設計C: スコープ整合性
Inv_C_ScopeConsistency ==
  \A i \in 1..Len(C_results): claims[C_results[i].claimId].scope \in requestedScopes

\* ========== カバレッジ検証（反例を期待） ==========

\* 設計A: 意味的に関連する候補を逃す可能性
\* Text一致しないがVector関連性がある候補がA_resultsに含まれない
Inv_A_SemanticCoverage ==
  \A c \in ClaimId:
    (InRequestedScope(c) /\ VectorRelevant(c) /\ ~TextRelevant(c))
    => \E i \in 1..Len(A_results): A_results[i].claimId = c
\* 注意: この不変条件は設計Aでは破られることを期待

\* 設計B: 完全一致候補を逃す可能性
\* Vector関連性がないがText完全一致する候補がB_resultsに含まれない
Inv_B_ExactMatchCoverage ==
  \A c \in ClaimId:
    (InRequestedScope(c) /\ TextRelevant(c) /\ ~VectorRelevant(c))
    => \E i \in 1..Len(B_results): B_results[i].claimId = c
\* 注意: この不変条件は設計Bでは破られることを期待

\* 設計C: 両方をカバー（マージ後のみ検証）
Inv_C_CompleteCoverage ==
  C_merged # {} =>
    \A c \in ClaimId:
      (InRequestedScope(c) /\ (TextRelevant(c) \/ VectorRelevant(c)))
      => c \in C_merged
\* Hybrid設計ではこの不変条件が成り立つ

\* ========== 融合正しさ ==========

\* 設計C: 融合スコアが正しく計算される
Inv_C_FusionCorrectness ==
  \A c \in C_merged:
    C_fusedScores[c] = FusedScore(C_textScores[c], C_vecScores[c])

\* ========== 全設計共通 ==========

\* 結果にスコープ外のClaimが含まれない
Inv_NoOutOfScopeClaims ==
  /\ (\A i \in 1..Len(A_results): claims[A_results[i].claimId].scope \in requestedScopes)
  /\ (\A i \in 1..Len(B_results): claims[B_results[i].claimId].scope \in requestedScopes)
  /\ (\A i \in 1..Len(C_results): claims[C_results[i].claimId].scope \in requestedScopes)

====

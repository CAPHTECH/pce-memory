---- MODULE api_flat ----
\* 設計A: フラットAPI
\* 全ての操作がどの状態からでも呼び出し可能
\* 制約は実行時にのみチェック

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  ClaimId,
  Scope,
  AllowTag

VARIABLES
  policyApplied,
  claims,
  activeContexts,
  lastCall,
  lastResult

vars == <<policyApplied, claims, activeContexts, lastCall, lastResult>>

\* 結果型
OK == "ok"
ERROR == "error"

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in SUBSET ClaimId
  /\ lastCall \in {"none", "policy", "upsert", "activate", "feedback"}
  /\ lastResult \in {OK, ERROR}

\* 初期状態
Init ==
  /\ policyApplied = FALSE
  /\ claims = {}
  /\ activeContexts = {}
  /\ lastCall = "none"
  /\ lastResult = OK

\* フラットAPI: どの状態からでも呼び出し可能
\* 問題: ポリシー適用前でもupsertを呼べてしまう

ApplyPolicy ==
  /\ policyApplied' = TRUE
  /\ lastCall' = "policy"
  /\ lastResult' = OK
  /\ UNCHANGED <<claims, activeContexts>>

\* Upsert: ポリシーチェックなしで呼べる（設計上の問題）
Upsert(cid) ==
  /\ cid \in ClaimId
  /\ \/ /\ policyApplied  \* 正常ケース
        /\ claims' = claims \cup {cid}
        /\ lastResult' = OK
     \/ /\ ~policyApplied  \* エラーケース（実行時エラー）
        /\ claims' = claims
        /\ lastResult' = ERROR
  /\ lastCall' = "upsert"
  /\ UNCHANGED <<policyApplied, activeContexts>>

\* Activate: 同様にポリシーチェックなし
Activate(scopeSet, allowSet) ==
  /\ \/ /\ policyApplied
        /\ claims # {}
        /\ lastResult' = OK
     \/ /\ ~policyApplied \/ claims = {}
        /\ lastResult' = ERROR
  /\ lastCall' = "activate"
  /\ UNCHANGED <<policyApplied, claims, activeContexts>>

\* Feedback
Feedback(cid) ==
  /\ \/ /\ policyApplied
        /\ cid \in claims
        /\ lastResult' = OK
     \/ /\ ~policyApplied \/ cid \notin claims
        /\ lastResult' = ERROR
  /\ lastCall' = "feedback"
  /\ UNCHANGED <<policyApplied, claims, activeContexts>>

Next ==
  \/ ApplyPolicy
  \/ \E cid \in ClaimId: Upsert(cid)
  \/ \E s \in SUBSET Scope, a \in SUBSET AllowTag: Activate(s, a)
  \/ \E cid \in ClaimId: Feedback(cid)

Spec == Init /\ [][Next]_vars

\* ========== 検証したい性質 ==========

\* 不変条件1: ポリシー適用前のupsert呼び出しは必ずエラー
\* フラットAPIではこれが「呼び出し可能」なことが問題
Inv_UpsertRequiresPolicy ==
  (lastCall = "upsert" /\ lastResult = OK) => policyApplied

\* 不変条件2: 成功したupsertの後はclaimsに追加されている
Inv_UpsertAddsClaimOnSuccess ==
  (lastCall = "upsert" /\ lastResult = OK) => claims # {}

\* 安全性: エラーが発生しうる（フラットAPIの欠点）
\* この性質が違反するなら、エラーパスが存在する
Inv_NoErrors == lastResult = OK

====

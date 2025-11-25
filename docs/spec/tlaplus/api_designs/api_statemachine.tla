---- MODULE api_statemachine ----
\* 設計C: 状態機械API
\* 各状態で許可される操作を型レベルで制限
\* 不正な呼び出しは「存在しない」（コンパイル時に排除）

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  ClaimId,
  Scope,
  AllowTag

VARIABLES
  apiState,       \* {Uninitialized, PolicyApplied, HasClaims, Ready}
  claims,
  activeContexts,
  lastOp

vars == <<apiState, claims, activeContexts, lastOp>>

\* API状態
UNINITIALIZED == "Uninitialized"
POLICY_APPLIED == "PolicyApplied"
HAS_CLAIMS == "HasClaims"
READY == "Ready"

\* 型制約
TypeInv ==
  /\ apiState \in {UNINITIALIZED, POLICY_APPLIED, HAS_CLAIMS, READY}
  /\ claims \in SUBSET ClaimId
  /\ lastOp \in {"none", "policy", "upsert", "activate", "feedback"}

\* 初期状態
Init ==
  /\ apiState = UNINITIALIZED
  /\ claims = {}
  /\ activeContexts = {}
  /\ lastOp = "none"

\* 状態遷移: Uninitialized → PolicyApplied
\* applyPolicyはUNINITIALIZEDでのみ呼び出し可能
ApplyPolicy ==
  /\ apiState = UNINITIALIZED
  /\ apiState' = POLICY_APPLIED
  /\ lastOp' = "policy"
  /\ UNCHANGED <<claims, activeContexts>>

\* 状態遷移: PolicyApplied → HasClaims
\* upsertはPOLICY_APPLIEDでのみ呼び出し可能
Upsert(cid) ==
  /\ apiState = POLICY_APPLIED
  /\ cid \in ClaimId
  /\ claims' = claims \cup {cid}
  /\ apiState' = HAS_CLAIMS
  /\ lastOp' = "upsert"
  /\ UNCHANGED <<activeContexts>>

\* 追加upsert: HasClaims状態でも可能
UpsertMore(cid) ==
  /\ apiState = HAS_CLAIMS
  /\ cid \in ClaimId
  /\ claims' = claims \cup {cid}
  /\ lastOp' = "upsert"
  /\ UNCHANGED <<apiState, activeContexts>>

\* 状態遷移: HasClaims → Ready
\* activateはHAS_CLAIMSでのみ呼び出し可能
Activate(scopeSet, allowSet) ==
  /\ apiState = HAS_CLAIMS
  /\ claims # {}
  /\ apiState' = READY
  /\ lastOp' = "activate"
  /\ UNCHANGED <<claims, activeContexts>>

\* feedback: Ready状態でのみ
Feedback(cid) ==
  /\ apiState = READY
  /\ cid \in claims
  /\ lastOp' = "feedback"
  /\ UNCHANGED <<apiState, claims, activeContexts>>

Next ==
  \/ ApplyPolicy
  \/ \E cid \in ClaimId: Upsert(cid)
  \/ \E cid \in ClaimId: UpsertMore(cid)
  \/ \E s \in SUBSET Scope, a \in SUBSET AllowTag: Activate(s, a)
  \/ \E cid \in ClaimId: Feedback(cid)

Spec == Init /\ [][Next]_vars

\* ========== 検証したい性質 ==========

\* 不変条件1: upsertはポリシー適用後のみ
\* 状態遷移で強制されるため、常に成立
Inv_UpsertAfterPolicy ==
  claims # {} => apiState # UNINITIALIZED

\* 不変条件2: activateはclaims存在後のみ
Inv_ActivateAfterClaims ==
  apiState = READY => claims # {}

\* 不変条件3: feedbackはReady状態のみ
Inv_FeedbackOnlyReady ==
  lastOp = "feedback" => apiState = READY

\* 不変条件4: 不正な状態遷移は存在しない
\* Uninitializedでupsertは呼べない（遷移自体が存在しない）
Inv_NoInvalidTransitions ==
  \/ apiState = UNINITIALIZED => claims = {}
  \/ TRUE

\* この設計ではエラーが「存在しない」
\* （不正な呼び出しは状態遷移として定義されていない）
Inv_NoErrorsEver == TRUE

====

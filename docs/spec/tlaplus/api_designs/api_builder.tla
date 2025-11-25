---- MODULE api_builder ----
\* 設計B: ビルダーパターンAPI
\* ClaimBuilder.text().scope().boundary().build()
\* 段階的に構築し、完全になるまでbuildできない

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  Text,
  Scope,
  BoundaryClass

VARIABLES
  \* ビルダー状態
  builderState,   \* {empty, hasText, hasScope, hasBoundary, complete}
  currentText,
  currentScope,
  currentBoundary,
  \* システム状態
  policyApplied,
  claims,
  lastResult

vars == <<builderState, currentText, currentScope, currentBoundary,
          policyApplied, claims, lastResult>>

\* ビルダー状態
EMPTY == "empty"
HAS_TEXT == "hasText"
HAS_SCOPE == "hasScope"
HAS_BOUNDARY == "hasBoundary"
COMPLETE == "complete"

\* 結果
OK == "ok"
ERROR == "error"

\* 型制約
TypeInv ==
  /\ builderState \in {EMPTY, HAS_TEXT, HAS_SCOPE, HAS_BOUNDARY, COMPLETE}
  /\ policyApplied \in BOOLEAN
  /\ lastResult \in {OK, ERROR}

\* 初期状態
Init ==
  /\ builderState = EMPTY
  /\ currentText = ""
  /\ currentScope = ""
  /\ currentBoundary = ""
  /\ policyApplied = FALSE
  /\ claims = {}
  /\ lastResult = OK

\* ポリシー適用
ApplyPolicy ==
  /\ policyApplied' = TRUE
  /\ UNCHANGED <<builderState, currentText, currentScope, currentBoundary, claims, lastResult>>

\* ビルダー: text設定（最初のステップ）
SetText(t) ==
  /\ builderState = EMPTY
  /\ t \in Text
  /\ builderState' = HAS_TEXT
  /\ currentText' = t
  /\ UNCHANGED <<currentScope, currentBoundary, policyApplied, claims, lastResult>>

\* ビルダー: scope設定（textの後）
SetScope(s) ==
  /\ builderState = HAS_TEXT
  /\ s \in Scope
  /\ builderState' = HAS_SCOPE
  /\ currentScope' = s
  /\ UNCHANGED <<currentText, currentBoundary, policyApplied, claims, lastResult>>

\* ビルダー: boundary設定（scopeの後）
SetBoundary(b) ==
  /\ builderState = HAS_SCOPE
  /\ b \in BoundaryClass
  /\ builderState' = HAS_BOUNDARY
  /\ currentBoundary' = b
  /\ UNCHANGED <<currentText, currentScope, policyApplied, claims, lastResult>>

\* ビルダー: build（全フィールド設定後のみ）
Build ==
  /\ builderState = HAS_BOUNDARY
  /\ \/ /\ policyApplied
        /\ builderState' = COMPLETE
        /\ claims' = claims \cup {currentText}
        /\ lastResult' = OK
     \/ /\ ~policyApplied
        /\ builderState' = EMPTY  \* リセット
        /\ lastResult' = ERROR
        /\ claims' = claims
  /\ UNCHANGED <<currentText, currentScope, currentBoundary, policyApplied>>

\* ビルダー: リセット
Reset ==
  /\ builderState' = EMPTY
  /\ currentText' = ""
  /\ currentScope' = ""
  /\ currentBoundary' = ""
  /\ UNCHANGED <<policyApplied, claims, lastResult>>

Next ==
  \/ ApplyPolicy
  \/ \E t \in Text: SetText(t)
  \/ \E s \in Scope: SetScope(s)
  \/ \E b \in BoundaryClass: SetBoundary(b)
  \/ Build
  \/ Reset

Spec == Init /\ [][Next]_vars

\* ========== 検証したい性質 ==========

\* 不変条件1: 不完全なビルドは不可能
\* buildが成功するのはHAS_BOUNDARYからのみ
Inv_CompleteRequiresAllFields ==
  builderState = COMPLETE =>
    (currentText # "" /\ currentScope # "" /\ currentBoundary # "")

\* 不変条件2: 順序の強制
\* SetScopeはHAS_TEXTからのみ
Inv_ScopeAfterText ==
  builderState = HAS_SCOPE => currentText # ""

\* 不変条件3: ビルド成功はポリシー適用後のみ
Inv_BuildRequiresPolicy ==
  (builderState = COMPLETE /\ lastResult = OK) => policyApplied

\* エラー発生可能性（ビルダーでもポリシー未適用ならエラー）
Inv_NoErrors == lastResult = OK

====

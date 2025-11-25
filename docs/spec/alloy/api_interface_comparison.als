module api_interface_comparison

-- ============================================================
-- API Interface Design Comparison
-- 3つのインターフェース設計を構造的に比較
-- ============================================================

-- 共通シグネチャ
sig ClaimId {}
sig Scope {}
sig AllowTag {}

-- Bool型の定義
abstract sig Bool {}
one sig True, False extends Bool {}

-- ============================================================
-- 設計A: フラットAPI
-- ============================================================

sig FlatAPIState {
  policyApplied: one Bool,
  claims: set ClaimId
}

-- どの状態からでも任意の操作を呼び出し可能
pred FlatAPI_CanCallUpsert[s: FlatAPIState] {
  -- 制約なし: いつでも呼べる
  some s
}

pred FlatAPI_CanCallActivate[s: FlatAPIState] {
  -- 制約なし: いつでも呼べる
  some s
}

-- フラットAPIの問題: ポリシー未適用でもupsert可能
assert FlatAPI_UnsafeUpsert {
  all s: FlatAPIState |
    FlatAPI_CanCallUpsert[s] implies s.policyApplied = True
}

-- ============================================================
-- 設計B: ビルダーパターンAPI
-- ============================================================

abstract sig BuilderState {}
one sig Empty, HasText, HasScope, HasBoundary, Complete extends BuilderState {}

sig BuilderAPIState {
  builderState: one BuilderState,
  policyApplied: one Bool
}

-- ビルダーの順序制約
pred Builder_CanSetText[s: BuilderAPIState] {
  s.builderState = Empty
}

pred Builder_CanSetScope[s: BuilderAPIState] {
  s.builderState = HasText
}

pred Builder_CanSetBoundary[s: BuilderAPIState] {
  s.builderState = HasScope
}

pred Builder_CanBuild[s: BuilderAPIState] {
  s.builderState = HasBoundary
}

-- ビルダーAPIの保証: 不完全なビルドは不可能
assert Builder_CompleteOnlyAfterAllFields {
  all s: BuilderAPIState |
    s.builderState = Complete implies
      -- HasBoundaryからのみ遷移可能（暗黙的に全フィールド設定済み）
      some prev: BuilderAPIState | prev.builderState = HasBoundary
}

-- ============================================================
-- 設計C: 状態機械API
-- ============================================================

abstract sig APIState {}
one sig Uninitialized, PolicyApplied, HasClaims, Ready extends APIState {}

sig StateMachineAPIState {
  currentState: one APIState,
  claims: set ClaimId
}

-- 状態ごとに許可される操作
pred SM_CanApplyPolicy[s: StateMachineAPIState] {
  s.currentState = Uninitialized
}

pred SM_CanUpsert[s: StateMachineAPIState] {
  s.currentState = PolicyApplied or s.currentState = HasClaims
}

pred SM_CanActivate[s: StateMachineAPIState] {
  s.currentState = HasClaims
  some s.claims
}

pred SM_CanFeedback[s: StateMachineAPIState] {
  s.currentState = Ready
}

-- 状態機械APIの保証: upsertはポリシー適用後のみ
assert SM_UpsertRequiresPolicy {
  all s: StateMachineAPIState |
    SM_CanUpsert[s] implies s.currentState != Uninitialized
}

-- 状態機械APIの保証: activateはclaims存在後のみ
assert SM_ActivateRequiresClaims {
  all s: StateMachineAPIState |
    SM_CanActivate[s] implies some s.claims
}

-- ============================================================
-- 設計比較
-- ============================================================

-- 比較1: 不正なupsert呼び出しの可能性
-- フラットAPIでは可能、状態機械APIでは不可能
pred CompareUpsertSafety {
  -- フラットAPI: ポリシー未適用でもupsert可能
  some s: FlatAPIState |
    s.policyApplied = False and FlatAPI_CanCallUpsert[s]

  -- 状態機械API: ポリシー未適用ではupsert不可能
  no s: StateMachineAPIState |
    s.currentState = Uninitialized and SM_CanUpsert[s]
}

-- 比較2: エラーパスの存在
-- フラットAPI: 実行時エラーあり
-- 状態機械API: コンパイル時に排除（エラーなし）
pred CompareErrorPaths {
  -- フラットAPI: エラーになる呼び出しが存在
  some s: FlatAPIState |
    s.policyApplied = False and FlatAPI_CanCallUpsert[s]

  -- 状態機械API: 不正な遷移は定義されていない
  no s: StateMachineAPIState |
    s.currentState = Uninitialized and SM_CanUpsert[s]
}

-- ============================================================
-- 検証コマンド
-- ============================================================

-- フラットAPIは安全ではない（反例が見つかる）
check FlatAPI_UnsafeUpsert for 4

-- ビルダーAPIの順序保証
check Builder_CompleteOnlyAfterAllFields for 4

-- 状態機械APIの安全性
check SM_UpsertRequiresPolicy for 4
check SM_ActivateRequiresClaims for 4

-- 比較実行
run CompareUpsertSafety for 4
run CompareErrorPaths for 4

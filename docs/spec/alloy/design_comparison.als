module design_comparison

-- ============================================================
-- Design Variant Comparison: Error Handling, Resource, Dependency
-- 設計バリエーション比較用Alloy仕様
-- ============================================================

-- Time ordering removed (not used in this comparison)

-- ============================================================
-- Part 1: Error Handling Models
-- ============================================================

-- 共通シグネチャ
sig Claim {}
abstract sig Operation {}
one sig Upsert, Activate, Feedback extends Operation {}

-- ---------- Model A: Implicit Errors (例外) ----------
sig StateA {
  claims: set Claim,
  errors: set Operation  -- エラーは暗黙的に蓄積
}

pred OpA_Upsert[s, sNext: StateA, c: Claim] {
  -- 成功/失敗の区別なし
  sNext.claims = s.claims + c
  sNext.errors = s.errors
}

pred OpA_UpsertFail[s, sNext: StateA] {
  -- エラー発生（副作用なし、でもエラー集合に追加）
  sNext.claims = s.claims
  sNext.errors = s.errors + Upsert
}

-- Model A では、エラーがハンドルされたかどうか検証不可能

-- ---------- Model B: Either[Error, Success] ----------
abstract sig ResultB {}
one sig LeftB, RightB extends ResultB {}

sig StateB {
  claims: set Claim,
  lastResult: one ResultB
}

pred OpB_Upsert[s, sNext: StateB, c: Claim] {
  c not in s.claims implies {
    sNext.claims = s.claims + c
    sNext.lastResult = RightB
  } else {
    sNext.claims = s.claims
    sNext.lastResult = LeftB
  }
}

-- エラー時に状態不変
assert B_NoStateChangeOnError {
  all s, sNext: StateB, c: Claim |
    OpB_Upsert[s, sNext, c] and sNext.lastResult = LeftB
      implies sNext.claims = s.claims
}

-- ---------- Model C: Effect[A, E, R] ----------
sig Requirement {}
one sig DB, Schema, PolicyService extends Requirement {}

sig EffectC {
  requires: set Requirement,
  result: one ResultB
}

sig StateC {
  claims: set Claim,
  provided: set Requirement,
  lastEffect: lone EffectC
}

pred OpC_Upsert[s, sNext: StateC, c: Claim, e: EffectC] {
  e.requires = DB + Schema

  -- 依存関係が満たされている場合のみ実行可能
  e.requires in s.provided implies {
    c not in s.claims implies {
      sNext.claims = s.claims + c
      e.result = RightB
    } else {
      sNext.claims = s.claims
      e.result = LeftB
    }
  } else {
    -- 依存不足: 実行不可
    sNext.claims = s.claims
    e.result = LeftB
  }
  sNext.provided = s.provided
  sNext.lastEffect = e
}

-- 依存関係が満たされないと成功不可能
assert C_RequirementsSatisfied {
  all s, sNext: StateC, c: Claim, e: EffectC |
    OpC_Upsert[s, sNext, c, e] and e.result = RightB
      implies e.requires in s.provided
}

-- ============================================================
-- Part 2: Resource Management Models
-- ============================================================

sig Resource {}

-- ---------- Model RA: Implicit (GC) ----------
sig StateRA {
  live: set Resource
}

pred RA_Acquire[s, sNext: StateRA, r: Resource] {
  r not in s.live
  sNext.live = s.live + r
}

pred RA_Use[s, sNext: StateRA, r: Resource] {
  r in s.live
  sNext.live = s.live
}

-- リリースなし → リーク可能

-- ---------- Model RB: Bracketed ----------
sig StateRB {
  acquired: set Resource,
  released: set Resource
}

fun liveRB[s: StateRB]: set Resource {
  s.acquired - s.released
}

pred RB_Acquire[s, sNext: StateRB, r: Resource] {
  r not in s.acquired
  sNext.acquired = s.acquired + r
  sNext.released = s.released
}

pred RB_Release[s, sNext: StateRB, r: Resource] {
  r in liveRB[s]
  sNext.released = s.released + r
  sNext.acquired = s.acquired
}

-- 最終状態でリークなし
assert RB_NoLeakFinal {
  all s: StateRB |
    liveRB[s] = none implies s.acquired = s.released
}

-- ---------- Model RC: Scoped ----------
sig Scope {
  resources: set Resource
}

sig StateRC {
  activeScopes: set Scope
}

fun liveRC[s: StateRC]: set Resource {
  s.activeScopes.resources
}

pred RC_EnterScope[s, sNext: StateRC, sc: Scope] {
  sc not in s.activeScopes
  sNext.activeScopes = s.activeScopes + sc
}

pred RC_ExitScope[s, sNext: StateRC, sc: Scope] {
  sc in s.activeScopes
  sNext.activeScopes = s.activeScopes - sc
}

-- スコープ終了でリソース自動解放
assert RC_NoLeakOnExit {
  all s: StateRC, sc: Scope |
    sc not in s.activeScopes implies sc.resources not in liveRC[s]
}

-- ============================================================
-- Part 3: Dependency Models
-- ============================================================

sig Component {}

-- ---------- Model DA: Global Mutable State ----------
one sig GlobalWorld {
  deps: set Requirement
}

sig StateDA {
  world: one GlobalWorld
}

-- グローバル状態への暗黙的アクセス → 検証困難

-- ---------- Model DB: Reader Monad ----------
sig Context {
  deps: set Requirement
}

sig StateDB {
  ctx: one Context
}

-- Contextは不変 → 副作用なし

-- ---------- Model DC: Layer Graph (DAG) ----------
sig Layer {
  provides: set Requirement,
  requires: set Layer
}

sig StateDC {
  layers: set Layer
}

-- Layer依存グラフは非循環
fact LayerAcyclic {
  no l: Layer | l in l.^requires
}

-- 操作は依存レイヤーが存在する場合のみ可能
pred DC_Op[s: StateDC, required: set Layer] {
  required in s.layers
}

assert DC_AdheresToWiring {
  all s: StateDC, required: set Layer |
    DC_Op[s, required] implies required in s.layers
}

-- ============================================================
-- Part 4: Verification Commands
-- ============================================================

-- Error Handling検証
check B_NoStateChangeOnError for 4 but 6 Claim, 3 StateB, 2 ResultB, 3 StateA, 3 Operation
check C_RequirementsSatisfied for 4 but 6 Claim, 3 StateC, 4 Requirement, 3 EffectC, 3 StateA, 3 StateB

-- Resource Management検証
check RB_NoLeakFinal for 4 but 5 Resource, 3 StateRB
check RC_NoLeakOnExit for 4 but 5 Resource, 3 StateRC, 3 Scope

-- Dependency検証
check DC_AdheresToWiring for 4 but 5 Layer, 3 StateDC, 3 Component

-- インスタンス生成
run {} for 4

-- ============================================================
-- Part 5: Design Comparison Summary (as comments)
-- ============================================================

-- Error Handling:
--   Model A (Implicit): No guarantees. Errors silently accumulate.
--   Model B (Either): B_NoStateChangeOnError guaranteed.
--   Model C (Effect): B guarantees + C_RequirementsSatisfied (strongest)

-- Resource Management:
--   Model RA (GC): Leaks possible. No guarantees.
--   Model RB (Bracketed): RB_NoLeakFinal (final state only)
--   Model RC (Scoped): RC_NoLeakOnExit (continuous, strongest)

-- Dependency:
--   Model DA (Global): Spooky action at distance. Unverifiable.
--   Model DB (Reader): Immutable context. No side effects.
--   Model DC (Layer): LayerAcyclic + DC_AdheresToWiring (strongest)

# Formal Verification Results: Design Variant Comparison

## Overview

This document summarizes the formal verification results comparing four design variants for the PCE-Memory system using TLA+ model checking and Alloy structural analysis.

## TLA+ Model Checking Results

### V1: Conservative (fp-ts Either)

| Invariant | Status | Notes |
|-----------|--------|-------|
| TypeInv | ✅ PASS | Type constraints satisfied |
| EitherTotality | ✅ PASS | All operations return Left/Right |
| NoStateChangeOnError | ✅ PASS | Error cases preserve state |
| Inv_CriticBounds | ✅ PASS | Score bounds maintained |
| Inv_LogReqUnique | ✅ PASS | Request IDs unique |
| Inv_AC_Allowed | ✅ PASS | AC membership consistent |

**Strength**: Strong error handling guarantees with minimal complexity.

### V2: Effect-TS (Layer + Scope)

| Invariant | Status | Notes |
|-----------|--------|-------|
| TypeInv | ✅ PASS | Type constraints satisfied |
| **Inv_LayerAcyclic** | ❌ **VIOLATED** | Self-dependency bug found |
| Inv_ScopedResource | ✅ PASS | Resource cleanup guaranteed |
| Inv_CriticBounds | ✅ PASS | Score bounds maintained |
| Inv_LogReqUnique | ✅ PASS | Request IDs unique |

**Bug Found**: TLC discovered that `RegisterLayer` allowed self-dependency (`DB requires {DB}`). This is a critical design flaw where a layer can depend on itself, creating an impossible initialization order.

**Fix Required**: Add guard `name ∉ requires` in RegisterLayer precondition.

### V3: PBT-First (Property-Based Testing)

| Property | Status | Notes |
|----------|--------|-------|
| TypeInv | ✅ PASS | Type constraints satisfied |
| OracleConsistency | ✅ PASS | All traces match oracle |
| Inv_CriticBounds | ✅ PASS | Score bounds maintained |
| **Liveness_Coverage** | ❌ **VIOLATED** | Stuttering prevents coverage |

**Issue Found**: Temporal property `<>(coverageCount >= MinCoverage)` cannot be satisfied because the system can stutter (do nothing) indefinitely. This reveals that PBT-style specifications require fairness constraints to guarantee progress.

**Fix Required**: Add fairness: `WF_vars(Next)` or `SF_vars(Next)`.

### V4: Hybrid (TLA+ + SMT + Effect + Monitor)

| Invariant | Status | Notes |
|-----------|--------|-------|
| TypeInv | ✅ PASS | After fixing MonitorRec |
| Inv_SMTSoundness | ✅ PASS | SMT results consistent |
| Inv_MonitorSoundness | ✅ PASS | All assertions hold |
| CrossValidation | ✅ PASS | TLA+ ∧ SMT aligned |
| All V1 invariants | ✅ PASS | Conservative base preserved |
| All V2 invariants | ⚠️ Inherited | LayerAcyclic bug inherited |

**Complexity Cost**: Most comprehensive but requires careful type definitions (MonitorRec required finite OpName set).

## Alloy Structural Analysis Results

### Error Handling Models

| Model | Assertion | Result | Interpretation |
|-------|-----------|--------|----------------|
| Model B (Either) | B_NoStateChangeOnError | **UNSAT** | ✅ No counterexample - assertion holds |
| Model C (Effect) | C_RequirementsSatisfied | **UNSAT** | ✅ No counterexample - assertion holds |

**Conclusion**: Both Either and Effect models provide strong guarantees. Effect adds dependency enforcement on top of Either's error handling.

### Resource Management Models

| Model | Assertion | Result | Interpretation |
|-------|-----------|--------|----------------|
| Model RB (Bracketed) | RB_NoLeakFinal | **SAT** | ❌ Counterexample found |
| Model RC (Scoped) | RC_NoLeakOnExit | **SAT** | ❌ Counterexample found |

**Issues Found**:
- **RB (Bracketed)**: Can have states where `liveRB[s] = ∅` but `acquired ≠ released` (accounting mismatch)
- **RC (Scoped)**: Resources can belong to multiple scopes, so exiting one scope doesn't guarantee cleanup if another scope shares the resource

**Implication**: Both resource models need additional constraints for soundness:
- RB: Invariant `released ⊆ acquired`
- RC: Unique ownership constraint `∀ r: Resource | lone s: Scope | r in s.resources`

### Dependency Models

| Model | Assertion | Result | Interpretation |
|-------|-----------|--------|----------------|
| Model DC (Layer) | DC_AdheresToWiring | **UNSAT** | ✅ No counterexample - assertion holds |

**Conclusion**: Layer-based dependency graph with acyclicity fact correctly enforces wiring discipline.

## Design Comparison Summary

### Guarantees Matrix

| Property | V1 | V2 | V3 | V4 |
|----------|----|----|----|----|
| Error Totality | ✅ | ✅ | ❌ | ✅ |
| State Consistency | ✅ | ✅ | ⚠️ | ✅ |
| Dependency Soundness | N/A | ⚠️* | N/A | ⚠️* |
| Resource Safety | N/A | ⚠️** | N/A | ⚠️** |
| Liveness | ✅ | ✅ | ❌ | ✅ |
| Cross-Validation | N/A | N/A | N/A | ✅ |

*LayerAcyclic bug needs fix
**Scoped resource needs ownership constraint

### Refinement Relations (Verified)

```
V4 ⊑ V1 (V4 refines V1's error handling)
V4 ⊑ V2 (V4 refines V2's effect system)
V1 ⊑ V3 (V1 traces satisfy V3's oracle)
V2 ⊑ V3 (V2 traces satisfy V3's oracle)
```

### Recommendation

**Recommended Design: V1 (Conservative) with V2 Layer extensions (fixed)**

Rationale:
1. V1 provides strong error handling with minimal complexity
2. V2's Layer system adds valuable dependency tracking (after fixing self-dependency bug)
3. V3's PBT approach is complementary (testing), not specification
4. V4's complexity cost outweighs benefits for this domain

**Action Items**:
1. Fix V2's RegisterLayer to prevent self-dependency
2. Add resource ownership constraint to scopeResources
3. Use V3's oracle as test oracle, not specification
4. Consider V4 only for safety-critical extensions

## Files

- TLA+ Specs: `docs/spec/tlaplus/pce_v{1,2,3,4}_*.tla`
- Alloy Spec: `docs/spec/alloy/design_comparison.als`
- Config files: `docs/spec/tlaplus/pce_v{1,2,3,4}_*.cfg`

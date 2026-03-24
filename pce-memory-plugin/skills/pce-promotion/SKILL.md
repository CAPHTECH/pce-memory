---
name: pce-promotion
context: fork
description: "Dedicated pce-memory v2 promotion pipeline skill. Guides distill -> promote -> rollback with candidate lineage, reviewer metadata, and durable repair rules. Triggered by: 'promotion pipeline', 'distill memory', 'promote candidate', 'rollback claim'."
argument-hint: '[distill|promote|rollback] [candidate or claim details]'
allowed-tools: 'mcp__pce-memory__pce_memory_observe, mcp__pce-memory__pce_memory_distill, mcp__pce-memory__pce_memory_promote, mcp__pce-memory__pce_memory_rollback, mcp__pce-memory__pce_memory_state, mcp__pce-memory__pce_memory_policy_apply'
---

# PCE Promotion - Distill, Promote, Rollback

Use this skill when the task is specifically about moving knowledge through the v2 promotion pipeline.

## Pipeline

`observe -> distill -> promote -> rollback`

`activate` and `feedback` live in `pce-core`; this skill focuses on the promotion boundary itself.

## State Gate

1. Check `pce_memory_state`
2. If `Uninitialized`, run `pce_memory_policy_apply`
3. Continue only after policy state is ready

## 1. Distill

Create a reviewable promotion candidate from one of these sources:

- `source_observation_ids`
- `source_claim_ids`
- `active_context_id`

### Recommended Inputs

```json
{
  "source_observation_ids": ["obs_..."],
  "proposed_kind": "fact",
  "proposed_scope": "project",
  "proposed_memory_type": "knowledge",
  "note": "why this should become durable"
}
```

### Distill Rules

- Distill is the required abstraction boundary between raw capture and durable memory.
- Use `working_state`, `knowledge`, `procedure`, or `norm` for durable intent.
- Do not propose `evidence` for durable promotion; it is reserved for micro memory.
- Candidate output is reviewable and includes invariant checks.
- `promotion_queue` is local governance state; it is not a sync surface.

## 2. Promote

Promote a pending candidate into durable meso or macro memory.

### Required Inputs

```json
{
  "candidate_id": "pq_...",
  "provenance": {
    "at": "2026-03-24T00:00:00Z",
    "actor": "claude"
  }
}
```

### Recommended Inputs

- `reviewers`: reviewer IDs or names, especially for principle/macro memory
- `review_note`: why promotion is justified

### Promotion Rules

- Project scope lands in meso memory.
- Principle scope lands in macro memory and should carry review lineage.
- Boundary monotonicity is enforced at promotion time.
- Secret-bearing candidates cannot silently become durable canonical memory.
- Promotion returns a `rollback_token`; keep it in mind when the claim is controversial or newly validated.

## 3. Rollback

Use rollback when a durable claim is wrong, stale in a harmful way, or superseded.

### Required Inputs

```json
{
  "claim_id": "clm_...",
  "reason": "superseded by corrected design",
  "provenance": {
    "at": "2026-03-24T00:00:00Z",
    "actor": "claude"
  }
}
```

### Rollback Rules

- Rollback is append-only and auditable.
- Do not delete or mutate history in place.
- Rolled-back claims drop out of canonical sync/export surfaces.
- Use rollback before re-promoting corrected knowledge when the prior durable claim should no longer be trusted.

## Decision Guide

- Raw note, log, or branch-local state: `observe`
- Candidate abstraction with lineage: `distill`
- Canonical durable memory: `promote`
- Incorrect canonical durable memory: `rollback`

## Common Failure Modes

- **Trying to promote raw text directly**: Observe first, then distill
- **Using `scope: session` as durable memory**: Session belongs in micro observation, not durable promotion
- **Using `secret` in durable writes**: Keep secrets in observe only
- **Skipping provenance**: `promote` and `rollback` require `provenance.at`

---
name: pce-core
context: fork
description: "Core pce-memory v2 workflow skill. Guides raw observe, distill/promote, intent-aware activate, feedback, rollback, and the narrow upsert escape hatch. Triggered by: 'memory workflow', 'activate context', 'record to memory', 'promotion pipeline'."
argument-hint: '[activate|observe|distill|promote|rollback|upsert|feedback] [query or text...]'
allowed-tools: 'mcp__pce-memory__pce_memory_observe, mcp__pce-memory__pce_memory_distill, mcp__pce-memory__pce_memory_promote, mcp__pce-memory__pce_memory_activate, mcp__pce-memory__pce_memory_feedback, mcp__pce-memory__pce_memory_rollback, mcp__pce-memory__pce_memory_upsert, mcp__pce-memory__pce_memory_state, mcp__pce-memory__pce_memory_policy_apply, mcp__pce-memory__pce_memory_upsert_entity, mcp__pce-memory__pce_memory_upsert_relation'
---

# PCE Core - V2 Knowledge Workflow

Manages the v2 pce-memory workflow:

`observe -> distill -> promote -> activate(intent) -> feedback -> rollback`

`pce_memory_upsert` still exists, but only as a narrow escape hatch for already-distilled durable knowledge.

## Argument Parsing

Parse `$ARGUMENTS`:

- `activate [query]` → Intent-aware recall mode
- `observe [text]` → Raw micro-memory capture
- `distill [source ids or guidance]` → Promotion candidate creation
- `promote [candidate-id]` → Durable promotion
- `rollback [claim-id] [reason]` → Durable repair/supersession
- `upsert [kind] [text]` → Escape hatch for already-distilled durable knowledge
- `feedback [claim-id] [signal]` → Feedback mode
- No arguments → Full workflow guide

## State Gate

1. Check current state with `pce_memory_state`
2. If `Uninitialized`, run `pce_memory_policy_apply`
3. Continue only after the policy state is ready for the tool you need

## 1. Observe (Raw Micro Memory Only)

Use `pce_memory_observe` for raw inputs:

- session work-in-progress
- chat/tool/file/http/system outputs
- debugging notes and local evidence
- secret or PII-bearing material that must not become durable inline

### Rules

- Observe is raw-only. It does not create durable claims inline.
- Do not use legacy inline extraction modes such as `single_claim_v0`.
- `extract: { mode: "noop" }` is only a compatibility knob and still preserves raw-only behavior.
- Use `boundary_class: secret` only in observe, never in upsert.
- Use observe instead of upsert for anything session-scoped.

### Typical Input

```json
{
  "source_type": "chat|tool|file|http|system",
  "content": "...",
  "boundary_class": "public|internal|pii|secret",
  "tags": ["..."],
  "ttl_days": 7
}
```

## 2. Distill (Create Promotion Candidate)

Use `pce_memory_distill` to convert observations, claims, or an active context into a reviewable candidate.

### Inputs

- `source_observation_ids`: Raw observations to abstract
- `source_claim_ids`: Existing durable claims to refine or supersede
- `active_context_id`: Promote from a planned working set
- `proposed_kind`: `fact | preference | task | policy_hint`
- `proposed_scope`: `project | principle`
- `proposed_memory_type`: `working_state | knowledge | procedure | norm`
- `note`: Distillation hint for reviewers

### Rules

- `evidence` is micro-only and cannot become a durable promoted claim.
- Distill preserves lineage and invariant checks in the candidate.
- Secret-bearing candidates may be created for review, but they cannot auto-promote into durable canonical memory.

## 3. Promote (Durable Meso/Macro Memory)

Use `pce_memory_promote` to accept a pending candidate and create a durable claim.

### Inputs

- `candidate_id` is required
- `provenance.at` is required
- `reviewers` and `review_note` are recommended, especially for macro/principle promotion

### Rules

- Project scope promotes into meso memory.
- Principle scope promotes into macro memory and should include review lineage.
- Boundary monotonicity is enforced at promotion time.
- Promotion returns a `rollback_token` for later repair.

## 4. Knowledge Recall (Activate)

Use `pce_memory_activate` as the task-facing recall planner.

### Current V2-Compatible Input Shape

The current API still uses `scope` and `allow`, and adds v2 planning controls:

```json
{
  "q": "...",
  "scope": ["project", "principle"],
  "allow": ["answer:task"],
  "intent": "resume_task|debug_incident|design_decision|policy_check",
  "kind_filter": ["task", "fact"],
  "memory_type_filter": ["working_state", "knowledge"],
  "include_observations": true,
  "top_k": 10
}
```

### Planner Guidance

- `intent` tunes ranking for the task shape.
- `kind_filter` narrows recall before ranking.
- `memory_type_filter` narrows semantic memory classes before ranking.
- `include_observations: true` pulls transient micro observations into recall when short-term context matters.
- Keep queries concrete: `"JWT auth token expiry"` is better than `"auth"`.

### Intent Hints

- `resume_task`: Use for branch/task recovery, often with `kind_filter: ["task"]` and `memory_type_filter: ["working_state"]`
- `debug_incident`: Use when recent evidence matters; often add `include_observations: true`
- `design_decision`: Bias toward durable design knowledge and procedures
- `policy_check`: Bias toward norms and policy hints

## 5. Feedback

Report quality of activated durable knowledge with `pce_memory_feedback`.

### Steps

1. Identify the `claim_id` from activated knowledge
2. Select the signal:
   - `helpful`: Contributed to problem solving
   - `harmful`: Was incorrect, caused bugs
   - `outdated`: Information is stale
   - `duplicate`: Same content exists in another claim
3. Call `pce_memory_feedback`

## 6. Rollback

Use `pce_memory_rollback` when a durable claim must be repaired or superseded without destructive mutation.

### Inputs

- `claim_id`
- `reason`
- `provenance.at`

### Rules

- Rollback is append-only and traceable.
- Rolled-back claims should disappear from sync/export surfaces and from future canonical recall.
- Use rollback after invalidation, bad promotion, or supersession by better knowledge.

## 7. Upsert Escape Hatch

Use `pce_memory_upsert` only for already-distilled durable knowledge when the full promotion pipeline is unnecessary.

### Allowed Cases

- Verified project knowledge (`scope: project`)
- Reviewed principle/policy knowledge (`scope: principle`)
- Optional graph updates through `pce_memory_upsert_entity` / `pce_memory_upsert_relation`

### Rejections and Guardrails

- `scope: session` is rejected. Use `pce_memory_observe` for session-scoped working context.
- `boundary_class: secret` is rejected. Use `pce_memory_observe` for secret material.
- Durable writes should include `memory_type` when known.
- `provenance.at` is required for project and principle writes.
- Keep text concise, specific, and in English.

## Workflow Patterns

See [workflow-patterns.md](references/workflow-patterns.md).

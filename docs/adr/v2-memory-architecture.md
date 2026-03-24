# ADR: V2 Memory Architecture Redesign

## Status

Accepted (2026-03-24)

## Context

Issue #49 replaces the v1 scope-centric memory model with a v2 architecture that matches the
validated product theory:

- micro memory is raw, local, and short-lived
- meso memory is the main durable project corpus
- macro memory is reviewed principle and policy knowledge
- promotion is distillation, not direct persistence
- activation must be planner-driven and intent-aware

Wave 1 and Wave 2 validation completed on 2026-03-24 and confirmed that the current repository
has four architectural mismatches:

1. `scope` is overloaded as storage boundary, lifecycle model, and retrieval planner input.
2. `observe` and `upsert` can bypass a real distill/promote boundary.
3. retrieval is pooled across selected scopes and applies boundary filtering after ranking.
4. active contexts persist too little metadata to explain or govern recall decisions later.

The same validation also identified two pre-v2 guardrail gaps that must be closed, or kept
closed, during the redesign:

- durable `secret` writes must remain rejected by default (#57)
- boundary filtering must move before ranking, so disallowed claims cannot consume candidate
  budget (#58)

Backward compatibility for the old public behavior is out of scope. Data migration is required,
but the v2 API should not preserve the old scope-first interaction model as a long-term shim.

## Decision

Adopt an explicit **micro / meso / macro architecture** with a governed promotion pipeline.

### Layer model

| Layer | Purpose                                                           | Storage posture                                  | Sync posture                | Retrieval role                          |
| ----- | ----------------------------------------------------------------- | ------------------------------------------------ | --------------------------- | --------------------------------------- |
| Micro | raw observations, evidence, live working context, active contexts | local, TTL-bound, volatile                       | never sync by default       | recent task context and evidence input  |
| Meso  | durable project knowledge and reusable procedures                 | durable, evidence-backed                         | default sync surface        | main recall corpus for development work |
| Macro | reviewed principles, invariants, and policy-adjacent norms        | append-only or separately governed durable store | explicit reviewed sync only | guardrail and constraint input          |

### Modeling rules

1. `scope` remains a compatibility and time-horizon field, but it is no longer the primary
   architectural primitive.
2. `kind = fact | preference | task | policy_hint` remains the coarse operator-facing vocabulary.
3. `memory_type = evidence | working_state | knowledge | procedure | norm` becomes the semantic
   axis that drives storage, retrieval, and promotion rules.
   `evidence` remains micro-first and is not a canonical durable claim target.
4. Promotion is compilation:
   raw material must be turned into a candidate artifact with abstraction, boundaries, provenance,
   and evidence before it becomes durable memory.
5. Direct durable canonical `session` writes are forbidden.
6. Direct raw writes into macro memory are forbidden.
7. `observe.extract.single_claim_v0` is removed.

### Core invariants

- micro capture stays separate from durable claims by default
- boundary class can upgrade, never downgrade
- `secret` content cannot silently become durable canonical memory
- every promoted item keeps lineage to source observations, claims, or active context
- rollback is append-only and traceable
- activation is boundary-first, layer-aware, type-aware, and intent-aware

## Target V2 API Surface

The v2 public workflow is:

`observe -> distill -> promote -> activate(intent) -> feedback -> rollback`

`search` can remain as a diagnostic or evaluation API, but it is not the primary task-facing
workflow. `upsert` is deprecated from normal agent guidance and may remain only as a narrowly
scoped escape hatch for already-distilled durable knowledge with the same promotion-time
validation rules.

### `observe`

Capture raw material into micro memory.

```json
{
  "content": "...",
  "source_type": "chat|tool_output|file_read|manual_note",
  "source_id": "...",
  "actor": "...",
  "boundary_class": "public|internal|pii|secret",
  "tags": ["..."],
  "ttl_days": 7
}
```

Returns:

- `observation_id`
- `effective_boundary_class`
- `expires_at`

Rules:

- stores only micro artifacts
- enforces boundary monotonicity and secret-safe capture
- does not create durable claims inline

### `distill`

Create a reviewable promotion candidate from observations, existing claims, or an active context.

```json
{
  "source_observation_ids": ["obs_..."],
  "source_claim_ids": ["clm_..."],
  "active_context_id": "ac_...",
  "proposed_kind": "fact|preference|task|policy_hint",
  "proposed_memory_type": "working_state|knowledge|procedure|norm",
  "target_layer": "meso|macro",
  "note": "optional operator guidance"
}
```

Returns:

- `candidate_id`
- `distilled_text`
- `proposed_kind`
- `proposed_memory_type`
- `proposed_boundary_class`
- `status`
- `invariant_check_results`

Rules:

- candidate status is explicit: `pending`, `accepted`, `rejected`
- candidate stores policy version, source lineage, and rejection state
- `secret` candidates cannot auto-promote

### `promote`

Move an accepted candidate into meso or macro durable memory.

```json
{
  "candidate_id": "pq_...",
  "reviewers": ["..."],
  "review_note": "...",
  "provenance": {
    "at": "2026-03-24T00:00:00Z",
    "actor": "claude",
    "note": "validated promotion"
  }
}
```

Returns:

- `claim_id`
- `target_layer`
- `is_new`
- `promoted_from`
- `rollback_token`

Rules:

- provenance is mandatory
- meso is the first durable landing zone for promoted knowledge
- macro promotion requires review lineage and approval metadata
- boundary monotonicity is enforced at promotion time

### `rollback`

Repair or supersede durable memory without destructive mutation.

```json
{
  "claim_id": "clm_...",
  "reason": "...",
  "provenance": {
    "at": "2026-03-24T00:00:00Z",
    "actor": "claude",
    "note": "rollback after invalidation"
  }
}
```

Returns:

- `rollback_id`
- `superseded_claim_id`
- `blast_radius`

Rules:

- append-only repair path
- records supersession or rollback ancestry
- invalidates affected active contexts and forces re-activation when needed

### `activate`

Plan an active context for a task, not just run pooled search.

```json
{
  "intent": "resume_task|debug_incident|design_decision|policy_check",
  "q": "...",
  "include_layers": ["micro", "meso", "macro"],
  "kind_filter": ["task", "fact"],
  "memory_type_filter": ["working_state", "knowledge"],
  "allow": ["answer:task"],
  "top_k": 12
}
```

Returns:

- `active_context_id`
- `intent`
- `expires_at`
- `policy_version`
- item list with `source_layer`, `source_id`, `rank`, `score_breakdown`,
  `selection_reason`, and provenance summary

Rules:

- boundary filtering runs before candidate generation and ranking
- candidates are generated per layer
- scoring is calibrated per layer and per type
- final merge uses intent-specific quotas and tie-break rules

### Intent profiles

| Intent            | Layer preference             | Type preference                               | Extra scoring factors                                               |
| ----------------- | ---------------------------- | --------------------------------------------- | ------------------------------------------------------------------- |
| `resume_task`     | micro > meso > macro         | `working_state`, `task`, relevant `knowledge` | recency, branch affinity, issue affinity, stale-task suppression    |
| `debug_incident`  | micro recent evidence + meso | `evidence`, `knowledge`, `procedure`          | error-token lexical match, incident recency, provenance quality     |
| `design_decision` | meso + macro                 | `knowledge`, `procedure`, `norm`              | evidence density, prior commitment overlap, low recency bias        |
| `policy_check`    | macro > meso                 | `norm`, `policy_hint`, supporting `knowledge` | deterministic prepend, authority, invariant match, fail-closed bias |

## Storage Schema Changes

### 1. Durable claims gain `memory_type`

Add `memory_type` to the durable claim shape and sync schema.

Durable claim values:

- `working_state`
- `knowledge`
- `procedure`
- `norm`

Reserved non-durable value:

- `evidence`

Interpretation:

- `kind` remains coarse compatibility metadata
- `memory_type` becomes the semantic control plane for promotion and retrieval
- `scope` remains a time-horizon and sync boundary hint, not the whole model
- `evidence` stays in micro storage (`observations` / `evidence`) and is cited by durable memory
  through evidence refs, rather than promoted as a canonical durable claim

### 2. Add `promotion_queue`

Introduce an explicit queue for distillation and promotion governance.

Required fields:

- `queue_id`
- `source_layer`
- `target_layer`
- `source_ids`
- `distilled_text`
- `candidate_hash`
- `proposed_kind`
- `proposed_memory_type`
- `proposed_scope`
- `proposed_boundary_class`
- `provenance_bundle`
- `evidence_ids`
- `policy_version_checked`
- `boundary_check_result`
- `status`
- `reviewers`
- `created_at`
- `resolved_at`
- `accepted_claim_id`
- `rejected_reason`

This queue is the choke point for:

- promotion review
- provenance enforcement
- rejection persistence
- rollback ancestry
- auditability of what was abstracted from what

### 3. Enrich active-context persistence

Replace the thin `active_contexts(id, claims_json)` model with:

- `active_contexts`
- `active_context_items`

`active_contexts` must store at least:

- `id`
- `intent`
- `query_text`
- `include_layers`
- `allow`
- `actor_hint`
- `expires_at`
- `policy_version`
- `created_at`

`active_context_items` must store at least:

- `ac_id`
- `source_layer`
- `source_id`
- `kind`
- `memory_type`
- `boundary_class`
- `rank`
- `fused_score`
- `score_breakdown`
- `selection_reason`
- `provenance_summary`

### 4. Durable layer separation

The target model separates:

- micro: `observations`, `evidence`, `active_contexts`, `active_context_items`
- meso: durable project memory
- macro: reviewed principle catalog

The first implementation may still use one DuckDB file, but automated promotion should not rely
on one flat durable corpus. Meso and macro must be exposed as separate namespaces, tables, or
append-only views before macro promotion is enabled.

## Migration Strategy

Migration is one-way: convert durable data and workflows to the new model, without preserving the
old public semantics as a long-lived compatibility layer.

### Phase 0: pre-v2 guardrails

Before cutover:

1. keep `upsert(secret)` rejected by default, with regression coverage (#57)
2. move boundary filtering before ranking in retrieval (#58)
3. enforce provenance on durable writes

### Phase 1: additive schema migration

1. add `memory_type` to durable claims
2. create `promotion_queue`
3. create `active_context_items`
4. extend `active_contexts` with `intent`, `expires_at`, and `policy_version`

This phase is additive so the repository can backfill and validate before removing old behavior.

### Phase 2: promotion pipeline rollout

1. add `distill`, `promote`, and `rollback`
2. route new durable promotion through `promotion_queue`
3. deprecate `observe.extract.single_claim_v0`
4. remove `single_claim_v0` only after `distill` is available and covered by tests

### Phase 3: claim backfill

Backfill durable claims with deterministic mappings where safe:

| Existing signal                         | Target `memory_type`                  | Notes                                                          |
| --------------------------------------- | ------------------------------------- | -------------------------------------------------------------- |
| `scope=principle` or `kind=policy_hint` | `norm`                                | macro or policy-adjacent durable knowledge                     |
| `kind=task`                             | `working_state`                       | requires lifecycle metadata and later stale/tombstone handling |
| `kind=fact`                             | `knowledge`                           | default durable project knowledge                              |
| `kind=preference`                       | review for `procedure` or `knowledge` | ambiguous cases should not be silently guessed                 |

Additional rules:

- keep evidence in `observations` and `evidence`; do not convert raw observations into durable
  claims during migration
- carry forward provenance, evidence IDs, and confidence metadata
- generate a review report for ambiguous `preference` and broad `fact` cases

### Phase 4: remove durable session canonical memory

Existing durable `scope=session` claims do not survive as canonical v2 memory.

Migration rule:

- recent and still-relevant items become `promotion_queue` candidates or short-lived
  `working_state` items after review
- stale or purely local residue is tombstoned or discarded
- active-context JSON snapshots are not migrated; they expire and are regenerated through
  `activate(intent)`

### Phase 5: retrieval cutover

1. add `intent`, `include_layers`, `kind_filter`, and `memory_type_filter` to `activate`
2. wire `retrieval.*` policy into runtime configuration
3. shift from one pooled ranker to per-layer candidate generation plus intent merge
4. persist item-level active-context metadata for feedback and analysis

### Phase 6: sync cutover

1. keep micro unsynced by default
2. keep meso as the default Git-based sync surface
3. enable macro sync only through reviewed promotion or explicit policy governance
4. preserve monotonic boundary upgrades during import and merge

## Implementation Plan

Execute the redesign in this order:

1. **Close guardrail gaps**
   - keep secret durable writes rejected with non-regression tests
   - move boundary filtering ahead of ranking
   - enforce provenance on durable writes

2. **Centralize domain taxonomy**
   - define `ClaimKind` and `MemoryType` in `src/domain`
   - stop duplicating string enums across handlers, sync schemas, and docs

3. **Add schema primitives**
   - add `memory_type`
   - add `promotion_queue`
   - add `active_context_items`
   - enrich `active_contexts`

4. **Implement the promotion pipeline**
   - add `distill`
   - add `promote`
   - add `rollback`
   - enforce provenance, boundary monotonicity, and rejection persistence
   - keep `single_claim_v0` only as a temporary compatibility path until `distill` is shipped

5. **Migrate stored data**
   - backfill `memory_type`
   - route durable session claims out of the canonical corpus
   - preserve lineage and evidence

6. **Implement the retrieval planner**
   - add `intent` and type filters to `activate`
   - pre-filter by boundary, layer, and type
   - score per layer and merge by intent quotas
   - persist score breakdowns and selection reasons

7. **Remove obsolete write shortcuts**
   - disable `observe.extract.single_claim_v0`
   - forbid direct durable canonical `session` writes

8. **Update sync and governance**
   - keep micro local only
   - treat meso as the default syncable layer
   - gate macro sync behind reviewed promotion

9. **Lock the design with tests and docs**
   - raw observations cannot bypass distill into durable memory
   - provenance is required for durable promotion
   - promotion preserves boundary monotonicity
   - rollback is append-only
   - activation persists item-level planner metadata

## Consequences

### Benefits

- aligns runtime architecture with the documented micro/meso/macro theory
- makes promotion auditable and reviewable
- reduces contamination of durable memory with task residue
- makes retrieval planner behavior explicit and tunable by policy
- creates a clean foundation for issues #40, #41, #42, and #45

### Costs

- more schema and lifecycle complexity
- migration work for existing claims and tooling
- additional review state for promotion and macro governance

These costs are acceptable because the validation results show that the current flat scope-centric
model cannot reliably enforce the intended pace-aware lifecycle.

## Validation Evidence

Primary evidence for this ADR:

1. [Issue #49](https://github.com/CAPHTECH/pce-memory/issues/49)
2. Issue #49 comment, 2026-03-24:
   <https://github.com/CAPHTECH/pce-memory/issues/49#issuecomment-4114982890>
3. [memory-layer-storage.md](../../validation/analysis/memory-layer-storage.md)
4. [memory-type-taxonomy.md](../../validation/analysis/memory-type-taxonomy.md)
5. [write-path-validation.md](../../validation/analysis/write-path-validation.md)
6. [retrieval-validation.md](../../validation/analysis/retrieval-validation.md)

Validated conclusions imported into this ADR:

- separate storage classes plus explicit `promotion_queue` are the recommended long-term boundary
- `memory_type` is required as a second axis beside `kind`
- the public write path must become `observe -> distill -> promote -> rollback`
- `activate` must become an intent-aware planner with boundary pre-filtering and item-level AC
  persistence
- policy retrieval settings must be wired into runtime before retrieval behavior can match the docs

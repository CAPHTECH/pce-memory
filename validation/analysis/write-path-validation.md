# Write Path Validation

> Historical note: this analysis captures the pre-v2 transition state. The runtime now has `distill`, `promote`, and `rollback`; references below to the removed observe extraction shortcut are retained only as design history.

## Recommendation

Choose `observe -> distill candidate -> review gate -> promote`, with `rollback` as an append-only repair path.

`pce_memory_upsert` should remain available only as a narrow escape hatch for already-distilled durable knowledge, not as the default path from raw observation to durable memory. The current repository implements `observe` and direct durable `upsert`, but it does not yet implement a first-class distill or promote stage.

## 1. Current Write Path Implementation vs Documented Intent

| Topic                             | Documented intent                                                                                                                                                                                                                                               | Current implementation                                                                                                                                                                                                                                                                                                                                                                                                | Validation result                                                                                     |
| --------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------- |
| Overall flow                      | Vision and policy docs describe pace-aware `distill` / `promote` / `rollback` with provenance and boundary checks (`docs/pce-memory-vision.md:35-46`, `docs/pce-memory-vision.md:147-151`, `docs/boundary-policy.md:35-45`, `docs/boundary-policy.md:257-258`). | Runtime has `handleObserve` plus direct `handleUpsert`; the dispatch table and tool registry define no `distill`, `promote`, or `rollback` handlers, and the DB schema defines no promotion queue or rollback tables (`apps/pce-memory/src/core/handlers.ts:468-870`, `apps/pce-memory/src/core/handlers.ts:1954-1970`, `apps/pce-memory/src/core/handlers.ts:2571-2922`, `apps/pce-memory/src/db/schema.sql:1-209`). | The documented write path is not implemented as explicit stages.                                      |
| Observe contract                  | `observe` is short-lived capture with optional extraction (`docs/mcp-tools.md:89-179`).                                                                                                                                                                         | Before the v2 promotion pipeline, `handleObserve` stored TTL-bound observations and also exposed a temporary inline claim-extraction shortcut.                                                                                                                                                                                                                                                                        | Observe existed, but it mixed capture with a shortcut instead of a separate distill stage.            |
| Promote contract                  | Distill should promote AC outcomes to LCP with dedupe, provenance, and boundary alignment (`docs/pce-memory-vision.md:149-151`, `docs/boundary-policy.md:38`).                                                                                                  | `handleUpsert` writes directly into the durable `claims` table after minimal validation and content hash dedupe (`apps/pce-memory/src/core/handlers.ts:137-247`, `apps/pce-memory/src/core/handlers.ts:321-456`, `apps/pce-memory/src/store/claims.ts:94-135`).                                                                                                                                                       | Promotion is currently direct durable persistence, not mediated promotion.                            |
| Provenance requirements           | Docs say upsert provenance is mandatory (`docs/pce-memory-vision.md:104-107`, `docs/pce-memory-vision.md:127-134`).                                                                                                                                             | Tool schema says `provenance.at` is required, but runtime `handleUpsert` does not validate `provenance` at all; it simply passes it through if present (`apps/pce-memory/src/core/handlers.ts:321-456`, `apps/pce-memory/src/core/handlers.ts:2667-2702`).                                                                                                                                                            | Runtime is weaker than the documented contract.                                                       |
| Secret handling on durable writes | Policy says `upsert` with `secret` is rejected by default (`docs/boundary-policy.md:35-39`, `docs/boundary-policy.md:233-240`).                                                                                                                                 | Runtime only checks that `boundary_class` exists in policy; it does not reject `secret` for `upsert` (`apps/pce-memory/src/core/handlers.ts:236-247`). A test intentionally upserts a `secret` claim successfully (`apps/pce-memory/test/activate-boundary-filter.test.ts:24-47`).                                                                                                                                    | Current durable path allows writes that policy describes as rejected.                                 |
| Session durability                | Pace docs distinguish short-lived AC / session-layer memory from durable LCP (`docs/pce-memory-vision.md:35-46`, `docs/boundary-policy.md:57-60`, `docs/boundary-policy.md:242-258`).                                                                           | Historically, `claims` had no TTL column and the old observe extraction shortcut wrote straight into `scope: 'session'` inside `claims`.                                                                                                                                                                                                                                                                              | That legacy design let session-scoped material become durable without an explicit promotion decision. |

The practical shape today is:

1. `observe` captures transient material in `observations`.
2. The old observe shortcut could also write a `session` claim immediately.
3. `upsert` writes directly into `claims`, which is the durable corpus used by activation and sync-adjacent flows.

That is closer to `observe -> optional raw extraction -> direct upsert` than `observe -> distill -> promote`.

## 2. Observe Stage: What Gets Captured, TTL, Boundary Handling

### What gets captured

`handleObserve` writes an `observations` row with:

- `id`, `source_type`, optional `source_id`
- stored `content` or `null`
- `content_digest`
- `content_length`
- optional `actor` and `tags`
- `expires_at`

This is implemented in `apps/pce-memory/src/core/handlers.ts:753-775` and persisted by `apps/pce-memory/src/store/observations.ts:24-61`. The physical schema matches that storage shape in `apps/pce-memory/src/db/schema.sql:198-209`.

In the legacy design, observe could also create:

- one `fact` claim
- always with `scope: 'session'`
- with `boundary_class` equal to the effective observed boundary
- plus one evidence record pointing back to the observation

That extraction path lives in `apps/pce-memory/src/core/handlers.ts:777-833`.

### TTL behavior

Current observe TTL is runtime-configured, not policy-driven:

- default `30` days from `PCE_OBS_TTL_DAYS`
- max `90` days from `PCE_OBS_TTL_DAYS_MAX`
- caller `ttl_days` is clamped against that max

See `apps/pce-memory/src/core/handlers.ts:599-621`.

Expired observations are scrubbed by nulling `content`, `actor`, `source_id`, and `tags`, while leaving the row, digest, length, and timestamps in place (`apps/pce-memory/src/store/observations.ts:75-100`).

This is materially different from the policy examples, which describe `session` as `7d` and `project` as `120d` (`docs/boundary-policy.md:57-60`, `docs/boundary-policy.md:175-189`). Observe does not read scope TTL policy at all; it reads env vars and performs a best-effort GC.

### Boundary handling

Observe has the strongest boundary behavior in the current write path:

- missing `boundary_class` defaults to `internal` (`apps/pce-memory/src/core/handlers.ts:656-661`)
- sensitivity detection can raise the effective class to `pii` or `secret` (`apps/pce-memory/src/core/handlers.ts:692-710`)
- `pii` forces redacted storage
- `secret` forces `digest_only`, replaces the digest with `sha256:REDACTED_SECRET`, and skips extraction (`apps/pce-memory/src/core/handlers.ts:719-781`)

This stage therefore already enforces a useful invariant: the effective boundary is monotonic and cannot be lower than the detected sensitivity.

### Observe-stage conclusion

Observe is the only stage that already resembles the intended architecture:

- it captures raw material separately from durable claims
- it has expiry and scrub behavior
- it upgrades boundaries defensively

But it still mixes two responsibilities:

- raw observation capture
- temporary one-shot claim creation

That shortcut is the main reason the distill boundary is still implicit instead of explicit.

## 3. Distill Stage: Does It Exist, and What Should It Look Like?

### Does it exist today?

Not as a first-class stage.

The old observe extraction shortcut in `handleObserve` was not enough to count as a real distill stage because it:

- does not create a separate candidate record
- does not record review state
- always emits `kind: 'fact'`
- always emits `scope: 'session'`
- does not perform abstraction beyond optional PII redaction
- does not record rejection reasons or reviewer decisions
- does not create rollback ancestry

It is better described as a wiring check or extraction shortcut, which matches the docs calling it a temporary mode (`docs/mcp-tools.md:173-179`).

### What distill should look like

Distill should produce a reviewable candidate, not a durable claim. The minimum output should be something like:

```ts
type DistillCandidate = {
  id: string;
  source_observation_ids: string[];
  source_claim_ids?: string[];
  active_context_id?: string;
  distilled_text: string;
  candidate_hash: string;
  proposed_kind: ClaimKind;
  proposed_scope: 'session' | 'project' | 'principle';
  proposed_boundary_class: 'public' | 'internal' | 'pii' | 'secret';
  provenance_bundle: Provenance;
  evidence_ids: string[];
  policy_version_checked: string;
  invariant_check_results: Record<string, 'pass' | 'fail'>;
  status: 'pending' | 'accepted' | 'rejected';
  reviewers?: string[];
  rejected_reason?: string;
  accepted_claim_id?: string;
  created_at: string;
  resolved_at?: string;
};
```

This matches the repository direction already argued in `validation/analysis/memory-layer-storage.md:17-19`, `validation/analysis/memory-layer-storage.md:48-75`, but the runtime code still lacks the candidate table, APIs, and lifecycle.

### Why distill must be separate

Without a distinct distill stage, the system cannot answer:

- what raw material led to this durable claim
- whether the text was abstracted or merely copied
- whether promotion was reviewed or auto-accepted
- why a candidate was rejected
- what to roll back when the promoted knowledge is later found invalid

That makes provenance shallow and rollback blind, which is exactly what the vision and policy docs are trying to avoid.

## 4. Promote Stage: Current vs Needed Promotion Mechanics

### Current promotion mechanics

There are only two practical promotion paths today:

1. direct `pce_memory_upsert`
2. the old `pce_memory_observe` extraction shortcut

Direct `upsert`:

- validates presence of `text`, `kind`, `scope`, and `boundary_class`
- auto-generates or verifies `content_hash`
- writes directly to `claims`
- dedupes only by `content_hash`
- optionally attaches graph memory

See `apps/pce-memory/src/core/handlers.ts:137-247`, `apps/pce-memory/src/core/handlers.ts:321-456`, and `apps/pce-memory/src/store/claims.ts:94-135`.

Legacy observe extraction shortcut:

- writes directly to `claims`
- always as `scope: 'session'`
- creates evidence linked to the originating observation

See `apps/pce-memory/src/core/handlers.ts:784-833`.

### What is missing from current promotion

Current promotion lacks:

- a candidate-to-claim transition
- explicit approval state
- promotion-specific invariant checks
- rollback tokens or supersession lineage
- durable rejection rules for `secret`
- required provenance enforcement
- runtime validation of `kind` / `scope` enums despite the tool schema advertising them (`apps/pce-memory/src/core/handlers.ts:2673-2676` vs `apps/pce-memory/src/core/handlers.ts:183-247`)

### Needed promotion mechanics

Promotion should be a separate write boundary with two allowed modes:

1. `promote(candidate_id, ...)`
   Use this for anything derived from observations, AC, or prior claims.

2. narrow direct durable `upsert(...)`
   Allow only when the caller already holds distilled durable knowledge, such as a reviewed ADR summary or a confirmed root-cause record with provenance. This should still enforce provenance and boundary rules.

Recommended API shape:

```ts
observe({
  source_type,
  source_id?,
  content,
  boundary_class?,
  actor?,
  tags?,
  ttl_days?,
}): {
  observation_id;
  effective_boundary_class;
  expires_at;
};

distill({
  source_observation_ids?,
  source_claim_ids?,
  active_context_id?,
  proposed_kind?,
  proposed_scope?,
  note?,
}): {
  candidate_id;
  distilled_text;
  proposed_kind;
  proposed_scope;
  proposed_boundary_class;
  invariant_check_results;
  status;
};

promote({
  candidate_id,
  provenance,
  reviewers?,
  review_note?,
}): {
  claim_id;
  is_new;
  promoted_from;
  rollback_token;
};

rollback({
  claim_id,
  reason,
  provenance,
}): {
  rollback_id;
  superseded_claim_id;
};
```

That API makes transition boundaries explicit and matches the issue acceptance criteria better than the current `observe` / `upsert` duality.

## 5. Invariants For Each Stage

### Observe invariants

| Invariant                                                         | Current status                                                                                                                           | Evidence                                                                                           |
| ----------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------- |
| Raw capture must stay separate from durable claims by default.    | Historically only partially satisfied. Observation storage was separate, but the old observe shortcut could still create a claim inline. | `apps/pce-memory/src/store/observations.ts:36-61`, legacy observe extraction path                  |
| Effective boundary must never be lower than detected sensitivity. | Satisfied.                                                                                                                               | `apps/pce-memory/src/core/handlers.ts:692-710`                                                     |
| Secret observation content must not be stored or extracted.       | Satisfied.                                                                                                                               | `apps/pce-memory/src/core/handlers.ts:719-781`                                                     |
| Observation retention must be finite and scrubbed after expiry.   | Satisfied, but env-driven rather than policy-driven.                                                                                     | `apps/pce-memory/src/core/handlers.ts:599-621`, `apps/pce-memory/src/store/observations.ts:75-100` |
| Observation evidence must not leak raw secret or PII.             | Mostly satisfied. Evidence snippet stores digest + byte length, not raw content.                                                         | `apps/pce-memory/src/core/handlers.ts:823-832`                                                     |

### Distill invariants

These are required but currently missing:

- every candidate must reference one or more source observations, claims, or an active context
- candidate text must be stored as an explicit candidate artifact with its own `candidate_hash`, even when it matches a concise source fragment
- proposed boundary must be monotonic relative to all source materials
- `secret` candidates cannot become auto-promotable
- rejection must be persisted, not silently dropped
- candidate status must be explicit: `pending`, `accepted`, or `rejected`
- policy version and invariant check results must be stored with the candidate

No current runtime object enforces these invariants.

### Promote invariants

| Invariant                                                              | Current status                                                            | Evidence                                                                                                                                       |
| ---------------------------------------------------------------------- | ------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------- |
| Durable promotion must require provenance.                             | Not satisfied in runtime.                                                 | `docs/pce-memory-vision.md:104-107`, `apps/pce-memory/src/core/handlers.ts:321-456`                                                            |
| Durable promotion must reject `secret` by default or route to review.  | Not satisfied in runtime.                                                 | `docs/boundary-policy.md:35-39`, `apps/pce-memory/src/core/handlers.ts:236-247`, `apps/pce-memory/test/activate-boundary-filter.test.ts:40-47` |
| Promotion target must be explicit and auditable.                       | Not satisfied. No candidate or promotion record exists.                   | `apps/pce-memory/src/core/handlers.ts:1954-1970`, `apps/pce-memory/src/core/handlers.ts:2571-2922`, `apps/pce-memory/src/db/schema.sql:1-209`  |
| Durable dedupe must preserve source lineage, not only final text hash. | Not satisfied. Current dedupe is only `content_hash` on `claims`.         | `apps/pce-memory/src/store/claims.ts:94-135`                                                                                                   |
| Boundary class may upgrade but must not downgrade during promotion.    | Not enforced at write time. Only sync has explicit monotonic handling.    | `apps/pce-memory/src/core/handlers.ts:236-247`, `apps/pce-memory/src/sync/merge.ts:14-42`                                                      |
| Rollback must be append-only and traceable.                            | Not satisfied. No rollback artifacts or linkage exist in write-path code. | `apps/pce-memory/src/core/handlers.ts:1954-1970`, `apps/pce-memory/src/core/handlers.ts:2571-2922`, `apps/pce-memory/src/db/schema.sql:1-209`  |

## 6. Missing Components

The repository is missing six concrete pieces needed for the intended write path:

1. A distill candidate store
   Needed to persist `distilled_text`, source lineage, invariant checks, review state, and rejection reasons before claim creation.

2. First-class `distill`, `promote`, and `rollback` handlers
   The runtime currently exposes `observe`, `upsert`, `activate`, and `feedback`, but not the transition tools the docs describe.

3. Promotion-time validation stronger than `content_hash`
   `handleUpsert` should validate runtime `kind`, `scope`, provenance requirements, and default rejection or review routing for `secret` and unredacted `pii`.

4. A richer active-context model
   The docs expect AC expiry and policy-aware lifecycle, but the implementation stores only `id` and serialized claims (`apps/pce-memory/src/store/activeContext.ts:5-17`, `apps/pce-memory/src/db/schema.sql:24-27`, `docs/schema.md:65-73`).

5. Promotion and rollback audit lineage
   The system needs `accepted_claim_id`, `rejected_reason`, `reviewers`, `rollback_of`, or equivalent fields somewhere durable.

6. Tests that lock the stage boundaries
   Missing tests include:
   - raw observation cannot bypass distill into project/principle memory
   - direct `upsert(secret)` is rejected or reviewed
   - provenance is mandatory for durable promotion
   - promotion preserves boundary monotonicity
   - rollback records supersession instead of mutating in place

## Evidence

- `apps/pce-memory/src/core/handlers.ts:137-247` shows `handleUpsert` validation is limited to required fields, hash matching, and policy boundary existence.
- `apps/pce-memory/src/core/handlers.ts:468-870` shows `handleObserve` already combines transient capture, boundary detection, TTL handling, and optional direct claim creation.
- The removed observe shortcut always extracted into `scope: 'session'`.
- That shortcut was framed as promotion, but in practice it was immediate direct claim creation without a separate distill/promote boundary.
- `apps/pce-memory/src/core/handlers.ts:2667-2702` advertises `provenance.at` as required for `pce_memory_upsert`, but the handler does not enforce it.
- `apps/pce-memory/src/store/observations.ts:36-61` and `apps/pce-memory/src/store/observations.ts:75-100` show short-lived observation storage plus scrub-on-expiry.
- `apps/pce-memory/src/store/claims.ts:94-135` shows durable claim dedupe is keyed only by final `content_hash`.
- `apps/pce-memory/src/store/activeContext.ts:5-17` and `apps/pce-memory/src/db/schema.sql:24-27` show AC is currently persisted without expiry or policy metadata.
- `apps/pce-memory/src/db/schema.sql:2-18` shows `claims` has no TTL field, so any successful claim write is durable.
- `apps/pce-memory/test/activate-boundary-filter.test.ts:24-47` proves current runtime accepts `secret` durable writes.
- `apps/pce-memory/src/sync/schemas.ts:119-125` suggests the intended durable-sharing surface is mainly `project` / `principle` and excludes `secret`; that default is more compatible with explicit promotion than with raw direct persistence.
- `README.md:115-140`, `docs/mcp-tools.md:89-179`, `docs/pce-memory-vision.md:35-46`, `docs/pce-memory-vision.md:102-150`, and `docs/boundary-policy.md:35-45` document a stronger staged write-path model than the current runtime implements.

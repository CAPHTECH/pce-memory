# Memory Layer Storage Validation

## Current Repository Signals

- `session / project / principle` already map to `micro / meso / macro` in `docs/core-types.md`.
- `observations` are already treated as short-lived data with TTL and scrub-on-expiry behavior in `docs/mcp-tools.md` and `apps/pce-memory/src/store/observations.ts`.
- `claims`, `evidence`, `entities`, and `relations` form the current durable corpus in `apps/pce-memory/src/db/schema.sql` and `apps/pce-memory/src/store/`.
- sync exports only `claims / entities / relations`; it does not export `observations` or `active_contexts`, and the default scope filter is `project,principle` in `apps/pce-memory/src/sync/schemas.ts`.
- the vision docs treat LCP as mainly meso/macro and AC as micro, with explicit distill and rollback, but the write path does not yet have a first-class promotion queue in code.

The current repository is therefore already halfway between "single store + tags" and "separate stores": micro is partially separated (`observations`, `active_contexts`), while meso and macro are still flattened into one durable `claims` corpus.

## 1. Candidate Architecture Comparison

| Candidate                                  | Write cost                                                                                    | Contamination risk                                                                                         | Sync behavior                                                                                                                    | Rollback                                                                                             | Retrieval fit                                                                                                                       | Schema complexity | Assessment                                                                                |
| ------------------------------------------ | --------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------- | ----------------- | ----------------------------------------------------------------------------------------- |
| Single durable store + layer tags          | Low. One write path and one schema.                                                           | High. Tentative micro findings and durable macro rules share the same corpus and can be recalled as peers. | Simple operationally, but relies on negative filters to keep micro local. Easy to accidentally over-sync if scope filters drift. | Weak. Rollback has to surgically edit the same corpus used for ordinary retrieval.                   | Fair for MVP search, weak for paced retrieval because macro guardrails, meso knowledge, and micro working context flatten together. | Low.              | Good bootstrap shape, not a good long-term boundary for pace-aware memory.                |
| Separate stores for micro / meso / macro   | Medium. Each layer can optimize its own writes, but promotion becomes cross-store copy logic. | Medium-low. Physical isolation helps, but direct writes into meso or macro can still bypass review.        | Better. Micro can stay local while meso and macro sync on different schedules.                                                   | Better. Layer-local restore is easier than corpus-wide edits.                                        | Good, but retrieval becomes a federated query problem across stores.                                                                | High.             | Stronger isolation, but still missing a governance choke point for promotion.             |
| Separate stores + explicit promotion queue | Medium-high. Adds one more write step for promoted knowledge.                                 | Low. Lower layers cannot silently become upper-layer memory; promotion is inspectable.                     | Best fit. Micro stays unsynced, meso can use current Git-based sync, macro can sync only after review.                           | Best fit. Queue records, snapshots, and append-only promotion history make downgrade paths explicit. | Best fit. Macro can act as guardrail input, meso as main durable corpus, micro as transient task context.                           | High.             | Recommended. The extra complexity matches the repository's stated distill/rollback model. |

## 2. Recommendation For Storage Boundaries Per Layer

Recommend **separate storage classes with an explicit promotion queue**.

### Micro

- Store raw and fast-changing task context in `observations` plus a fully modeled `active_contexts / active_context_items` shape.
- Keep it **local, volatile, and non-syncable**.
- Do not write raw micro content directly into the durable `claims` corpus by default.
- Promotion from micro must first create a queue record that carries distilled text, provenance, and boundary checks.

### Meso

- Use the durable collaborative memory layer for `project` knowledge.
- Back it with the current `claims / evidence / entities / relations` pattern, but treat it as the **first durable landing zone** for promoted knowledge.
- This is the main syncable corpus because it is where repeated team or repository knowledge belongs.
- Direct upsert is acceptable here when the knowledge is already stable enough to be durable.

### Macro

- Split macro from meso as a **separate governance store or append-only namespace**, even if the first implementation still lives in the same DuckDB file.
- Macro should hold slow-moving `principle` memory, invariants, and policy-adjacent decisions.
- Only meso to macro promotion or reviewed policy updates may write here.
- Retrieval should treat macro as constraint-setting input, not as just another flat search hit.

### Implementation note

If the repository wants an incremental path, keep one DB file at first but introduce:

1. a real `promotion_queue`
2. a complete `active_contexts` schema with `expires_at`, `policy_version`, `scope`, and ranked items
3. separate meso and macro namespaces or tables before allowing automated promotion

The API boundary matters more than whether the first split is "table" or "database file".

## 3. Required Metadata Per Layer

| Layer | Required metadata                                                                                                                                                                                                             | Why it is required                                                                                                                                                  |
| ----- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Micro | `layer`, `session_id` or `window`, `actor`, `source_type`, `source_id`, `created_at`, `expires_at`, `boundary_class`, `content_digest`, `content_length`, `task_hint`                                                         | Micro memory is volatile and may contain sensitive raw material, so expiry, provenance-lite source tracking, and scrub-safe digests matter more than reuse scoring. |
| Meso  | `layer`, `kind`, `scope=project`, `boundary_class`, `content_hash`, `provenance`, `evidence_ids`, `utility`, `confidence`, `recency_anchor`, `distilled_from`, `sync_visibility`                                              | Meso memory is the reusable team corpus. It needs dedupe, evidence, critic signals, and enough lineage to explain how micro findings became durable claims.         |
| Macro | `layer`, `kind`, `scope=principle`, `boundary_class`, `content_hash`, `provenance`, `evidence_ids`, `approved_by`, `approval_count`, `policy_version_checked`, `effective_from`, `supersedes` or `rollback_of`, `review_note` | Macro memory is slow, normative, and high-blast-radius. Approval lineage and rollback ancestry are mandatory, not optional.                                         |

### Promotion Queue Metadata

The queue is not a layer, but it is required by the recommended architecture. Each queue record should carry:

- `queue_id`, `source_layer`, `target_layer`
- `source_ids` and `distilled_text`
- `candidate_hash`
- `proposed_kind`, `proposed_scope`, `proposed_boundary_class`
- `provenance_bundle` and `evidence_ids`
- `policy_version_checked`, `boundary_check_result`
- `status`, `reviewers`, `created_at`, `resolved_at`
- `accepted_claim_id` or `rejected_reason`

## 4. Sync / TTL / Rollback Rules Per Layer

| Layer | Sync rules                                                                                                                                                     | TTL rules                                                                                                                                                                              | Rollback rules                                                                                                                                              |
| ----- | -------------------------------------------------------------------------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Micro | No Git sync. Do not export `observations` or task-local AC snapshots. Only queue records may cross the boundary.                                               | AC should expire in hours, and raw observations should default to days, not months. Use the documented session target (`7d`) as the architectural default, with scrub-on-expiry.       | Rollback is discard-first: expire AC, scrub observations, cancel queue items, and re-activate from durable layers.                                          |
| Meso  | Git-based CRDT sync is appropriate here. Default export/import should stay scoped to `project`, with boundary filtering and boundary-class monotonic upgrades. | Use the documented `project` default (`120d`) as the base TTL. Completed tasks should tombstone early; durable facts/preferences can live longer if refreshed by evidence or feedback. | Append tombstones or superseding claims instead of destructive edits. Preserve provenance and evidence chains. Boundary class may upgrade, never downgrade. |
| Macro | No automatic developer hook sync. Macro sync should happen only through reviewed promotion, signed policy updates, or another explicit governance channel.     | No routine TTL. Treat macro as durable until explicitly superseded or rolled back.                                                                                                     | Roll back by restoring a prior approved version or snapshot, recording blast radius, and forcing downstream re-activation against the restored macro set.   |

## 5. Reasons For Rejecting Alternatives

### Why not single durable store + tags

- The repository already shows that micro does not behave like durable memory: `observations` are TTL-based and `active_contexts` are meant to expire, while sync already avoids exporting them.
- A single flat durable corpus makes retrieval too eager to mix tentative session findings with institutional constraints.
- Rollback becomes ambiguous because the same store mixes "working memory", "team memory", and "institutional memory".
- It does not match the documented claim that AC is micro and LCP is mainly meso/macro.

### Why not separate stores without a promotion queue

- Physical separation alone does not stop an agent from writing unstable micro findings straight into meso or macro.
- The repository's distill and rollback story depends on inspectable promotion, provenance, and review. A direct cross-store write path loses that checkpoint.
- Without queue records, there is no canonical place to attach reviewer state, policy checks, rejection reasons, or rollback ancestry.

## Evidence

- `docs/core-types.md`: `session / project / principle` already encode the intended micro / meso / macro mapping.
- `docs/pce-memory-vision.md`: pace-aware promotion and rollback are part of the product contract; AC is short-term and LCP is durable.
- `docs/pce-model.ja.md`: LCP is mainly meso/macro, AC is micro, and promotion must be mediated through boundary objects and review.
- `docs/boundary-policy.md`: layer tempos, scope TTL, append-only rollback expectations, and review requirements are already defined at the policy level.
- `docs/mcp-tools.md`: `observe` is explicitly short-TTL, `activate` expects expiring AC, and policy examples already differentiate `session / project / principle` TTLs.
- `docs/schema.md`: the intended `active_contexts` schema is richer than the current implementation and already assumes expiry plus policy versioning.
- `apps/pce-memory/src/store/observations.ts`: expired observations are scrubbed by nulling `content`, `actor`, `source_id`, and `tags`.
- `apps/pce-memory/src/store/activeContext.ts`: the current AC store persists only `id` plus serialized `claims`, without `expires_at`, `policy_version`, or ranked items.
- `apps/pce-memory/src/store/claims.ts`: durable claims persist `content_hash`, `provenance`, `utility`, `confidence`, and `recency_anchor`.
- `apps/pce-memory/src/store/feedback.ts`: feedback updates claim `utility`, `confidence`, and `recency_anchor`.
- `apps/pce-memory/src/store/rerank.ts`: retrieval scoring explicitly consumes `utility`, `confidence`, and recency decay.
- `apps/pce-memory/src/db/schema.sql`: durable claims, evidence, graph memory, policy storage, and volatile observations are already separate concerns in schema terms.
- `apps/pce-memory/src/sync/schemas.ts`: the default sync scope filter is `project,principle`, and `secret` is blocked from sync.
- `apps/pce-memory/src/sync/push.ts`: sync export writes only `claims`, `entities`, and `relations`.
- `apps/pce-memory/src/sync/pull.ts`: sync import merges claims by `content_hash` and upgrades `boundary_class` when incoming data is stricter.
- `apps/pce-memory/src/sync/merge.ts`: boundary merging is monotonic and never downgrades strictness.

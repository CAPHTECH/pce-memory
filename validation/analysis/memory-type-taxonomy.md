# Memory Type Taxonomy Validation

> Historical note: promotion and lifecycle observations below describe the pre-v2 transition period unless explicitly noted otherwise.

## Current Repository Signals

- The user-facing workflow currently presents four claim kinds: `fact`, `preference`, `task`, and `policy_hint` in `AGENTS.md:43-63`.
- The design docs repeat the same four-value claim-kind taxonomy and keep `scope` (`session`, `project`, `principle`) as a separate axis in `docs/core-types.md:140-153`, `docs/mcp-tools.md:315-318`, and `docs/schema.md:215-217`.
- The runtime code does not centralize claim kinds in `src/domain`; `apps/pce-memory/src/domain/types.ts:1-22` only defines entity types. Claim kind enums are duplicated in handlers, sync schemas, and docs.
- Durable claims are stored in one `claims` table with `kind`, `scope`, `boundary_class`, ranking fields (`utility`, `confidence`, `recency_anchor`), and provenance, while `observations`, `evidence`, and `active_contexts` are separate tables in `apps/pce-memory/src/db/schema.sql:2-27` and `apps/pce-memory/src/db/schema.sql:178-199`.
- Retrieval is scope-first and boundary-filtered: `activate` validates `scope`, runs hybrid search, then applies boundary allow checks in `apps/pce-memory/src/core/handlers.ts:875-935`.
- Kind-specific retrieval behavior is currently limited to recency half-lives in `apps/pce-memory/src/store/rerank.ts:11-18` and `docs/activation-ranking.md:126-130`.
- The existing review already notes that `observe` extraction is still primitive and that retrieval and active-context management are weaker than the docs imply in `docs/pce-memory-usefulness-review.ja.md:48-60`.

## 1. Current Type Taxonomy Coverage

### Current claim kinds

| Kind          | Intended meaning today                                   | Evidence          | Coverage assessment                                                                                                               |
| ------------- | -------------------------------------------------------- | ----------------- | --------------------------------------------------------------------------------------------------------------------------------- |
| `fact`        | Architecture decisions, technical constraints, API specs | `AGENTS.md:43-47` | Strong for durable semantic knowledge. Too broad because it also absorbs decisions, constraints, root causes, and specs.          |
| `preference`  | Coding style, tool choices, naming conventions           | `AGENTS.md:49-53` | Adequate for subjective defaults, but procedural knowledge often gets mixed in here even when it is not merely a preference.      |
| `task`        | Work in progress and TODO items                          | `AGENTS.md:55-58` | Adequate for "current work item" labeling, but weak for lifecycle because open/closed/blocked state is not modeled.               |
| `policy_hint` | Security requirements and operational rules              | `AGENTS.md:60-63` | Adequate for normative guidance, but it lumps enforceable policy, principle-level guidance, and local operational rules together. |

### Coverage against Issue #53 target examples

| Desired memory type from Issue #53 | Current representation                             | Coverage | Why                                                                                                             |
| ---------------------------------- | -------------------------------------------------- | -------- | --------------------------------------------------------------------------------------------------------------- |
| Episodic evidence                  | `observations` plus `evidence`, not a claim kind   | Partial  | The system has separate evidence stores, but the claim taxonomy itself has no first-class "evidence" type.      |
| Working state                      | `task` plus `session` scope plus `active_contexts` | Partial  | The pieces exist, but there is no explicit working-state model with status, freshness, or completion semantics. |
| Semantic project knowledge         | Mostly `fact` at `project` scope                   | Strong   | This is the clearest fit in the current taxonomy.                                                               |
| Procedural knowledge               | Split between `fact` and `preference`              | Weak     | Procedures, playbooks, and conventions are not distinguished from factual knowledge or subjective preference.   |
| Normative / principle knowledge    | `policy_hint` and/or `principle` scope             | Partial  | Scope and kind both carry part of the meaning, so the semantic boundary is blurry.                              |

### Main coverage conclusion

The current four kinds are a workable operator-facing MVP, but they are not yet a full memory-type taxonomy independent of time horizon. The repository already treats `kind`, `scope`, and storage class as different concerns, but only `scope` is consistently reflected in storage and retrieval. The semantic space requested by Issue #53 is therefore only partially captured by `kind`.

## 2. Do current types map well to storage, retrieval, and lifecycle?

### Storage

| Question                                               | Current behavior                                                                                                                                                                                  | Assessment                                                                   |
| ------------------------------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------------------------------------------------------------------- |
| Does kind choose the storage class?                    | No. All durable claims share one `claims` table in `apps/pce-memory/src/db/schema.sql:2-18`.                                                                                                      | Weak mapping.                                                                |
| Does kind choose the sync layout?                      | No. Sync exports by `scope`, not by `kind`, and defaults to `project` and `principle` only in `apps/pce-memory/src/sync/schemas.ts:119-125` and `apps/pce-memory/src/sync/fileSystem.ts:171-178`. | Weak mapping.                                                                |
| Is episodic material separated from durable knowledge? | Yes. `observations` are separate, TTL-based records, and `evidence` is separate from `claims` in `apps/pce-memory/src/db/schema.sql:178-199`.                                                     | Good, but this is a storage-class distinction, not a claim-kind distinction. |
| Is active context a first-class typed store?           | Not yet. Runtime AC storage is only `{id, claims}` in `apps/pce-memory/src/store/activeContext.ts:5-16`.                                                                                          | Weak mapping.                                                                |

Storage is therefore driven mainly by `observation vs claim`, `scope`, and `boundary_class`, not by the current four kinds.

### Retrieval

| Question                                            | Current behavior                                                                                                                                                                  | Assessment       |
| --------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ---------------- |
| Do candidate generators differ by kind?             | No. Text and vector search both filter on `scope` and rank candidates without type-specific query logic in `apps/pce-memory/src/store/hybridSearch.ts:300-425`.                   | Weak mapping.    |
| Does activate filter or request by kind?            | No. `activate` accepts `scope`, `allow`, `q`, `top_k`, and `cursor`, but not `kind`, in `apps/pce-memory/src/core/handlers.ts:875-924`.                                           | Weak mapping.    |
| Does kind affect reranking?                         | Yes, but only through recency half-life: `fact=120`, `task=14`, `preference=90`, `policy_hint=365` in `apps/pce-memory/src/store/rerank.ts:11-18`.                                | Partial mapping. |
| Are retrieval parameters type-aware through policy? | Not in current runtime defaults. The policy defaults contain hybrid settings, but not kind-specific retrieval strategies, in `packages/pce-policy-schemas/src/defaults.ts:23-31`. | Weak mapping.    |

Retrieval today is effectively "scope + boundary + text/vector similarity + critic + kind-specific recency decay". That is useful, but it is not enough to say each memory type has a preferred retrieval strategy.

### Lifecycle

| Question                                               | Current behavior                                                                                                                                                                        | Assessment                |
| ------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------- |
| Do different kinds have different promotion rules?     | Historically no. The old observe extraction shortcut always created `kind='fact'` and `scope='session'`, which was a weak mapping.                                                      | Weak mapping.             |
| Do different kinds have different update rules?        | No. Feedback updates `utility`, `confidence`, and sometimes `recency_anchor` uniformly across all claims in `apps/pce-memory/src/store/feedback.ts:10-61`.                              | Weak mapping.             |
| Is task completion or task staleness modeled?          | Not in code. The review doc explicitly calls out the need for `task` completion handling in `docs/pce-memory-usefulness-review.ja.md:114-117`.                                          | Missing.                  |
| Are session/project/principle TTLs enforced on claims? | The policy defines scope TTL defaults in `packages/pce-policy-schemas/src/defaults.ts:7-10`, but claim rows have no per-claim expiry field in `apps/pce-memory/src/db/schema.sql:2-18`. | Partial and inconsistent. |

Lifecycle is the weakest part of the current taxonomy. `task` is the clearest example: it has a faster recency decay than `fact`, but it does not yet have open/closed/tombstoned semantics.

## 3. Missing types or categories needed

The repository should not explode the existing four-value `kind` enum immediately, because that enum is repeated in docs, MCP tool schemas, sync schemas, rerank logic, and health/reporting output schemas (`docs/mcp-tools.md:315-318`, `apps/pce-memory/src/core/handlers.ts:2674`, `apps/pce-memory/src/sync/schemas.ts:17-19`, `apps/pce-memory/src/store/rerank.ts:11-18`, `apps/pce-memory/src/core/handlers.ts:2966`). Expanding `kind` directly would create a large compatibility blast radius.

The cleaner path is to keep the current `kind` enum as a coarse compatibility axis and add a second semantic axis such as `memory_type`.

### Recommended semantic memory types

| Proposed `memory_type` | Current approximation                 | Canonical representation                                       | Required metadata                                                                               | Allowed layers     | Promotion eligibility                                           |
| ---------------------- | ------------------------------------- | -------------------------------------------------------------- | ----------------------------------------------------------------------------------------------- | ------------------ | --------------------------------------------------------------- |
| `evidence`             | `observations` and `evidence` tables  | Observation or evidence record, not a durable claim by default | `source_type`, `source_id`, `content_digest`, `content_length`, `recorded_at`, `observation_id` | Session first      | Promotable only through explicit distillation into another type |
| `working_state`        | `task` kind plus AC                   | Durable or semi-durable claim for active work state            | `status`, `issue_id`, `branch`, `blocked_on`, `last_confirmed_at`, `owner`                      | Session, Project   | Promotable to `knowledge` or `procedure` when resolved          |
| `knowledge`            | Mostly `fact`                         | Durable semantic knowledge claim                               | `provenance`, `confidence`, `evidence_ids`, optional `entities`                                 | Project, Principle | Promotable from evidence or resolved work                       |
| `procedure`            | Split across `fact` and `preference`  | Reusable workflow, playbook, or convention                     | `trigger`, `steps`, `tool`, `expected_outcome`, `success_count` or `verified_at`                | Project, Principle | Promotable after repeated success or explicit review            |
| `norm`                 | `policy_hint`, some `principle` facts | Rule, invariant, compliance requirement, or principle          | `authority`, `enforcement`, `effective_from`, `supersedes`, `policy_version_checked`            | Project, Principle | Direct only with review or policy linkage                       |

### Why these categories

- `evidence` is already present in storage, but not in the claim taxonomy. Making it explicit prevents raw observations from being mistaken for durable knowledge.
- `working_state` is needed because `task` today names a category of content, but not its lifecycle state.
- `knowledge` is the stable center of what `fact` already does well.
- `procedure` is the most obvious missing category in the current four-kind model.
- `norm` separates "what must hold" from "what we prefer" and "what we observed".

### Suggested subtype examples

Subtypes can stay out of the primary enum at first, but the repository would benefit from a small controlled vocabulary:

- `knowledge`: `decision`, `constraint`, `root_cause`, `spec`
- `working_state`: `next_step`, `blocked_on`, `hypothesis`, `todo`
- `procedure`: `playbook`, `convention`, `checklist`
- `norm`: `security_rule`, `operational_rule`, `principle`

This lines up with the review doc's own recommended recording targets: `design decision`, `convention`, `bug root cause`, and `task state` in `docs/pce-memory-usefulness-review.ja.md:93-95`.

## 4. Retrieval and search model implications per type

| Memory type     | Preferred retrieval model                                                             | Recency posture               | Important metadata or indexes                                          | Why                                                                                                                             |
| --------------- | ------------------------------------------------------------------------------------- | ----------------------------- | ---------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------- |
| `evidence`      | Provenance-first lookup, time-window filters, source filters                          | Very high recency sensitivity | `observation_id`, `source_type`, `source_id`, `recorded_at`            | Evidence is most useful when it can be cited and traced, not when it wins a generic semantic search.                            |
| `working_state` | Session/project-biased search with strong recency and open-status filters             | Highest recency sensitivity   | `status`, `issue_id`, `branch`, `last_confirmed_at`                    | Work state becomes stale quickly and should not outrank durable knowledge just because embeddings are similar.                  |
| `knowledge`     | Balanced hybrid search plus critic/rerank and graph support                           | Moderate recency sensitivity  | `entities`, `evidence_ids`, `confidence`, `utility`                    | This is the core reusable corpus.                                                                                               |
| `procedure`     | Lexical-first or hybrid with command/token awareness                                  | Medium recency sensitivity    | `tool`, `trigger`, `steps`, optional `success_count`                   | Procedures are often retrieved by exact tool names, commands, or identifiers rather than by abstract semantic similarity alone. |
| `norm`          | Deterministic prepend, rule retrieval, or must-include recall before ordinary ranking | Low recency sensitivity       | `authority`, `enforcement`, `effective_from`, `policy_version_checked` | Normative memory should act as a guardrail, not merely as another ranked hit.                                                   |

### Current-runtime implication

If the repository keeps the current search pipeline, new memory types will not actually change recall behavior because `activate` and `hybridSearch` do not branch on type today. A semantic taxonomy therefore needs at least one of the following:

1. Type-aware candidate filters or boosts in `activate`
2. Type-aware rerank terms beyond recency
3. Deterministic inclusion rules for `norm`
4. Separate retrieval entry points for `evidence` and `working_state`

Without that, a richer taxonomy would remain documentation-only.

## 5. Recommendations

### Recommended direction

Adopt a two-axis model:

- Keep `kind = ClaimKind` for backward compatibility and coarse operator workflows.
- Add `memory_type = MemoryType` as the semantic taxonomy that drives storage and retrieval design.

### Concrete recommendations

1. Centralize taxonomy definitions in `src/domain`.
   - Today `apps/pce-memory/src/domain/types.ts:1-22` does not define claim kind at all, so the taxonomy is duplicated across docs, handlers, sync schemas, and rerank code.

2. Make promotion explicit by type.
   - Observe should stay raw-only, and promotion should emit a typed candidate or queue entry instead of forcing `fact/session`.

3. Give `working_state` real lifecycle metadata.
   - Add at minimum `status`, `last_confirmed_at`, and a tombstone or completion path.
   - The current system already has generic tombstone slots in sync schemas (`apps/pce-memory/src/sync/schemas.ts:63-65`), and the review doc already calls out completed-task handling as missing work (`docs/pce-memory-usefulness-review.ja.md:114-117`).

4. Make retrieval type-aware, not just kind-recency-aware.
   - The current kind half-life model is useful but too coarse. Keep it as a default fallback, not as the full retrieval strategy.

5. Keep storage-class distinctions explicit.
   - `evidence` should stay primarily in `observations` and `evidence`.
   - `knowledge`, `procedure`, and `norm` belong in durable claims.
   - `working_state` may live in claims, but needs stronger lifecycle controls than ordinary `fact`.

6. Move retrieval policy from hard-coded constants toward configuration.
   - The review doc already calls out that retrieval is too constant-driven today in `docs/pce-memory-usefulness-review.ja.md:54-60`.
   - Type-aware retrieval will be easier to evolve if it is policy-driven.

### Minimum implementation sequence

To make the recommendations actionable, the smallest repository-aligned change sequence is:

1. Add `ClaimKind` and `MemoryType` definitions to `apps/pce-memory/src/domain/types.ts`, then import them from `apps/pce-memory/src/core/handlers.ts` and `apps/pce-memory/src/sync/schemas.ts` instead of repeating string literals.
2. Extend the durable claim shape with an optional `memory_type` field in `apps/pce-memory/src/db/schema.sql`, `apps/pce-memory/src/store/claims.ts`, `apps/pce-memory/src/core/handlers.ts`, and `apps/pce-memory/src/sync/schemas.ts`.
3. Keep `pce_memory_observe` raw-only and route durable promotion through a typed promotion candidate instead of forcing `fact/session`.
4. Extend `pce_memory_activate` and the hybrid search path to accept optional `kind` and `memory_type` filters, plus deterministic prepend rules for `norm`.
5. Add at least one task-lifecycle path for `working_state`: open, complete, and stale or tombstoned. The existing sync tombstone shape is a reasonable starting point.
6. Update docs and validation prompts last, after runtime types and MCP schemas stop drifting.

### Recommendation summary

The current four claim kinds should be treated as a coarse compatibility layer, not as the final semantic taxonomy. They are good enough for today's manual upsert workflow, but they do not yet satisfy Issue #53's requirement that each memory type have a clear storage pattern, retrieval pattern, and promotion rule. The missing move is not "more kinds everywhere"; it is a clean separation between:

- storage class: observation, evidence, claim, active context
- time horizon: session, project, principle
- semantic memory type: evidence, working_state, knowledge, procedure, norm

## Evidence

- `AGENTS.md:43-63`
- `docs/core-types.md:140-153`
- `docs/mcp-tools.md:315-318`
- `docs/schema.md:215-217`
- `docs/activation-ranking.md:126-130`
- `docs/agent-guide.md:242`
- `docs/pce-memory-usefulness-review.ja.md:48-60`
- `docs/pce-memory-usefulness-review.ja.md:93-95`
- `docs/pce-memory-usefulness-review.ja.md:114-121`
- `apps/pce-memory/src/domain/types.ts:1-22`
- `apps/pce-memory/src/db/schema.sql:2-27`
- `apps/pce-memory/src/db/schema.sql:115-137`
- `apps/pce-memory/src/db/schema.sql:178-199`
- `apps/pce-memory/src/core/handlers.ts:137-196`
- `apps/pce-memory/src/core/handlers.ts:797-807`
- `apps/pce-memory/src/core/handlers.ts:875-935`
- `apps/pce-memory/src/store/claims.ts:94-170`
- `apps/pce-memory/src/store/hybridSearch.ts:300-425`
- `apps/pce-memory/src/store/rerank.ts:11-18`
- `apps/pce-memory/src/store/feedback.ts:10-61`
- `apps/pce-memory/src/store/activeContext.ts:5-16`
- `apps/pce-memory/src/core/handlers.ts:2674`
- `apps/pce-memory/src/core/handlers.ts:2966`
- `apps/pce-memory/src/sync/schemas.ts:17-19`
- `apps/pce-memory/src/sync/schemas.ts:52-65`
- `apps/pce-memory/src/sync/schemas.ts:119-125`
- `apps/pce-memory/src/sync/fileSystem.ts:171-178`
- `packages/pce-policy-schemas/src/defaults.ts:7-10`
- `packages/pce-policy-schemas/src/defaults.ts:23-31`
- `apps/pce-memory/test/observe.test.ts:506-530`

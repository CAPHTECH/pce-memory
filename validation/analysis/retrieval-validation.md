# Retrieval Validation

## Current Repository Signals

- `pce_memory_activate` accepts `scope`, `allow`, `top_k`, `q`, `cursor`, and `include_meta`; it does not accept `kind`, `memory_type`, or `intent` (`apps/pce-memory/src/core/handlers.ts:875-931`, `apps/pce-memory/src/core/handlers.ts:2779-2806`).
- The current retrieval path is `handleActivate -> hybridSearchPaginated -> hybridSearchWithScores -> hybridSearch` (`apps/pce-memory/src/core/handlers.ts:923-945`, `apps/pce-memory/src/store/hybridSearch.ts:801-949`).
- `textSearch` and `vectorSearch` both filter only by `scope`; neither query path filters by `boundary_class`, `kind`, or any type axis before ranking (`apps/pce-memory/src/store/hybridSearch.ts:274-365`, `apps/pce-memory/src/store/hybridSearch.ts:379-443`).
- `kind` affects reranking only through recency half-lives (`fact=120`, `task=14`, `preference=90`, `policy_hint=365`) (`apps/pce-memory/src/store/rerank.ts:11-18`, `apps/pce-memory/src/store/rerank.ts:130-148`).
- `claims` storage has `kind`, `scope`, and `boundary_class`, but no `memory_type` field (`apps/pce-memory/src/db/schema.sql:2-18`, `apps/pce-memory/src/store/claims.ts:24-40`).
- Repository docs already define `session/project/principle` as `micro/meso/macro`, and the validation corpus already assumes distinct intents such as `resume_task`, `debug_incident`, `design_decision`, and `policy_check` (`docs/core-types.md:148-154`, `validation/rubric.md:129-145`, `docs/local-validation-ollama.md:139-175`).

## 1. Current Retrieval Implementation

### Request contract and flow

`activate` validates only `scope` and `allow`, calls hybrid search with the requested scopes, and then applies boundary allow-tag filtering after ranking (`apps/pce-memory/src/core/handlers.ts:901-931`). The runtime saves the resulting active context as `{ id, claims }` JSON without item-level layer metadata, rank breakdowns, or policy metadata (`apps/pce-memory/src/core/handlers.ts:933-945`, `apps/pce-memory/src/store/activeContext.ts:5-16`, `apps/pce-memory/src/db/schema.sql:24-27`).

### Candidate generation

| Stage           | Current behavior                                                                               | Evidence                                                                                                 | Assessment                                       |
| --------------- | ---------------------------------------------------------------------------------------------- | -------------------------------------------------------------------------------------------------------- | ------------------------------------------------ |
| Text search     | Splits `q` on whitespace and matches any token with `ILIKE ... OR ...` within requested scopes | `apps/pce-memory/src/store/hybridSearch.ts:290-346`                                                      | Scope-aware only                                 |
| Text score      | Uses `critic.score` or default `0.5` as `text_score`, then orders by that score                | `apps/pce-memory/src/store/hybridSearch.ts:295-305`, `apps/pce-memory/src/store/hybridSearch.ts:333-344` | Lexical match decides admission, not strength    |
| Vector search   | Uses normalized cosine similarity over `claim_vectors`, filtered only by scope                 | `apps/pce-memory/src/store/hybridSearch.ts:395-424`                                                      | Semantic candidate generation is also scope-only |
| Merge           | Unions text and vector candidate IDs and computes `S = alpha * vec + (1 - alpha) * text`       | `apps/pce-memory/src/store/hybridSearch.ts:458-507`, `apps/pce-memory/src/store/hybridSearch.ts:589-674` | Single pooled ranking                            |
| Rerank          | Multiplies fused score by `g(utility, confidence, recency(kind))`                              | `apps/pce-memory/src/store/hybridSearch.ts:625-664`, `apps/pce-memory/src/store/rerank.ts:98-148`        | Partial kind-aware rerank only                   |
| Boundary filter | Filters ranked results by `allow` tags after retrieval                                         | `apps/pce-memory/src/core/handlers.ts:925-931`                                                           | Boundary-aware, but too late in the pipeline     |

### Boundary filtering behavior

Boundary allow-tag checks work functionally and are covered by tests (`apps/pce-memory/test/activate-boundary-filter.test.ts:20-72`). However, the filter runs after `hybridSearchPaginated` has already selected and paginated results (`apps/pce-memory/src/core/handlers.ts:923-931`, `apps/pce-memory/src/store/hybridSearch.ts:908-949`). That creates three concrete problems:

1. Disallowed claims can consume candidate budget before allowed claims are considered.
2. `next_cursor` and `has_more` are computed on the unfiltered ranked list, not the final allowed list.
3. Boundary is not a true precondition on retrieval despite the spec requiring boundary-first selection (`docs/activation-ranking.md:21-45`).

## 2. Layer-Awareness: Does Retrieval Distinguish Micro / Meso / Macro?

### What exists today

The repository clearly defines `scope` as the pace-layer proxy: `session = micro`, `project = meso`, `principle = macro` (`docs/core-types.md:148-154`). Retrieval respects the requested scopes, so it is not completely layer-blind (`apps/pce-memory/src/core/handlers.ts:907-924`, `apps/pce-memory/src/store/hybridSearch.ts:300-303`, `apps/pce-memory/src/store/hybridSearch.ts:417-421`).

### What is missing

Current retrieval is still a pooled cross-layer ranker:

- all selected scopes feed one shared text candidate pool and one shared vector candidate pool
- all candidate IDs are merged into one set
- one global fused score decides the final order
- utility z-score statistics are computed across the whole selected scope set, not per layer (`apps/pce-memory/src/store/hybridSearch.ts:523-539`, `apps/pce-memory/src/store/hybridSearch.ts:609-674`)

This means the system distinguishes layers only at admission time, not at scoring or selection time. A `session` claim and a `principle` claim compete as peers once both are inside the same scope set.

### Assessment

Layer-awareness is **partial**:

- Strong enough to say "search only `project`" or "include `session` too"
- Too weak to say "micro is recent working context, macro is guardrail context, meso is reusable project memory"

### Retrieval strategy comparison

| Strategy                                           | Layer behavior                                                                        | Relevance               | Cross-layer leakage | Complexity | Fit for current validation corpus         |
| -------------------------------------------------- | ------------------------------------------------------------------------------------- | ----------------------- | ------------------- | ---------- | ----------------------------------------- |
| Current pooled corpus ranking                      | `scope` only gates admission; all selected layers share one ranker                    | Good for generic recall | High                | Low        | Weak for `resume_task` and `policy_check` |
| Pooled ranking with layer quotas and boosts        | Still one corpus, but add per-layer caps and weights                                  | Better                  | Medium              | Medium     | Viable incremental step                   |
| Per-layer candidate generation plus merged ranking | Generate and score micro/meso/macro separately, then merge with quotas and tie-breaks | Best                    | Low                 | Higher     | Best fit                                  |

### Recommendation

Choose **per-layer candidate generation plus merged ranking** as the target planner. It matches Issue #49's proposed direction and the validation corpus better than pooled search because the tasks already imply different layer mixes:

- `resume_task`: micro + meso, low macro quota
- `debug_incident`: recent micro evidence + meso bug knowledge, macro only when policy or invariant relevance is explicit
- `design_decision`: meso + macro first
- `policy_check`: macro first, meso second, micro usually excluded

The incremental bridge from current code is to keep using `scope` as the temporary layer proxy while changing the planner from "one pooled ranker" to "three layer-local candidate lists plus merge rules".

## 3. Type-Awareness: Does Retrieval Use `kind` / `memory_type`?

### `kind`

`kind` exists in storage and in every retrieved claim (`apps/pce-memory/src/db/schema.sql:2-18`, `apps/pce-memory/src/store/claims.ts:24-40`). But current retrieval uses it only in rerank recency decay:

- `fetchClaimMetrics` reads `kind`
- `calculateGFromClaim` converts `kind` into a half-life
- tests verify kind-specific decay behavior (`apps/pce-memory/src/store/hybridSearch.ts:547-563`, `apps/pce-memory/src/store/rerank.ts:81-148`, `apps/pce-memory/test/gRerank.integration.test.ts:144-154`)

There is no server-side `kind` filter in `activate`, which is the gap already captured by Issue #45.

### `memory_type`

`memory_type` does not exist in runtime storage, domain types, or retrieval contracts:

- no schema column in `claims`
- no field in `Claim`
- no domain enum
- no activate/search filter (`apps/pce-memory/src/db/schema.sql:2-18`, `apps/pce-memory/src/store/claims.ts:24-40`, `apps/pce-memory/src/domain/types.ts:1-22`, `apps/pce-memory/src/core/handlers.ts:875-931`)

### Assessment

Type-awareness is **minimal**:

- `kind` is a rerank hint, not a retrieval planner
- `memory_type` is absent
- candidate generation, pagination, and final selection are not type-aware

### Recommendation

Use a two-stage model:

1. Short-term: add server-side `kind[]` filtering and boosting to `activate` and hybrid search.
2. Medium-term: add `memory_type` as a second axis so retrieval can distinguish at least `working_state`, `knowledge`, `procedure`, `evidence`, and `norm`.

### Required scoring factors by type

| Current / future type      | Retrieval factors that should matter                                                           | Why                                                               |
| -------------------------- | ---------------------------------------------------------------------------------------------- | ----------------------------------------------------------------- |
| `task` / `working_state`   | recency, open status, issue or branch match, owner affinity                                    | Work state gets stale quickly                                     |
| `fact` / `knowledge`       | semantic similarity, utility, confidence, evidence density                                     | Core durable project memory                                       |
| `preference` / `procedure` | lexical tool-token match, trigger match, success or verification recency                       | Procedures and conventions are often retrieved by exact terms     |
| `policy_hint` / `norm`     | deterministic inclusion for policy intents, authority, provenance strength, low recency weight | Normative memory should act as a constraint, not just another hit |
| `evidence`                 | source proximity, observation recency, provenance completeness                                 | Evidence should be citeable before it is highly ranked            |

## 4. Intent-Awareness: Does Retrieval Adapt To User Intent?

### Signals in the repository

The repository already has intent-like task categories:

- validation tasks: `resume_task`, `debug_incident`, `design_decision`, `policy_check` (`validation/rubric.md:129-145`, `docs/local-validation-ollama.md:139-175`)
- prompt helpers such as `debug_assist` that suggest an `activate` call for debugging (`apps/pce-memory/src/core/handlers.ts:2095-2104`, `apps/pce-memory/src/core/handlers.ts:2440-2462`)

### Current runtime behavior

Intent does not exist in the retrieval API. Every caller uses the same contract:

- same `activate` input shape
- same scope-only candidate generation
- same fixed alpha / k values
- same pooled merge
- same kind-recency rerank (`apps/pce-memory/src/core/handlers.ts:875-931`, `apps/pce-memory/src/store/hybridSearch.ts:701-949`)

`debug_assist` is therefore a prompt wrapper, not an intent-aware planner. It changes the query string and suggested scopes, but not the retrieval algorithm itself.

### Assessment

Intent-awareness is **absent in runtime retrieval**.

### Recommendation

`activate` should accept an explicit `intent` and translate it into planner rules. The most practical shape on the current schema is:

```json
{
  "intent": "resume_task | debug_incident | design_decision | policy_check",
  "q": "...",
  "include_layers": ["micro", "meso", "macro"],
  "kind_filter": ["task", "fact"],
  "memory_type_filter": ["working_state", "knowledge"],
  "top_k": 12
}
```

### Required scoring factors by intent

| Intent            | Layer preference             | Type preference                          | Extra scoring factors                                                        |
| ----------------- | ---------------------------- | ---------------------------------------- | ---------------------------------------------------------------------------- |
| `resume_task`     | micro > meso > macro         | `task`, `working_state`, relevant `fact` | recency, branch or issue affinity, stale-task suppression                    |
| `debug_incident`  | micro recent evidence + meso | `evidence`, `knowledge`, `procedure`     | error-token lexical match, incident recency, provenance quality              |
| `design_decision` | meso + macro                 | `fact`, `procedure`, `norm`              | evidence density, existing commitment overlap, lower recency bias            |
| `policy_check`    | macro > meso                 | `norm`, `policy_hint`, supporting `fact` | deterministic prepend, authority, boundary/invariant match, fail-closed bias |

## 5. Current Scoring Model Analysis

### Implemented formula

The current runtime formula is:

1. Text candidates receive `text_score = critic.score` or `0.5`
2. Vector candidates receive `vec_score = norm_cos(cos_sim(...))`
3. Fused score is `S = 0.65 * s_vec + 0.35 * s_text`
4. Final score is `score_final = S * g`
5. `g = utility_term * confidence_term * recency_term`
6. `recency_term` uses `kind` half-lives (`apps/pce-memory/src/store/hybridSearch.ts:295-344`, `apps/pce-memory/src/store/hybridSearch.ts:621-664`, `apps/pce-memory/src/store/rerank.ts:11-18`, `apps/pce-memory/src/store/rerank.ts:98-148`)

### Strengths

- Hybrid search exists and is simple enough to validate locally.
- Utility, confidence, and recency signals are all wired into reranking.
- Kind-specific recency is already implemented and tested.

### Current model weaknesses

| Area                 | Current behavior                                                                            | Why it is a problem                                                                                             |
| -------------------- | ------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| Lexical scoring      | Query-time text ranking is ordered by critic score, not lexical strength                    | Two matched claims with identical critic scores are effectively tied even if one is a much better textual match |
| Dynamic tuning       | `ALPHA`, `THRESHOLD`, `K_TEXT`, and `K_VEC` are hard-coded constants in runtime             | Docs describe policy-driven and dynamic tuning, but runtime does not consume it                                 |
| Policy integration   | Retrieval policy exists in `PolicyDocument`, but runtime state stores only `BoundaryPolicy` | `retrieval.*` cannot currently affect live scoring                                                              |
| Boundary timing      | Boundary filtering happens after ranking                                                    | Disallowed items can crowd out allowed results                                                                  |
| Layer calibration    | Utility z-score stats are computed over all selected scopes together                        | Micro noise and macro norms can affect each other through shared statistics                                     |
| Diversity / dedupe   | No MMR or content-hash dedupe at retrieval time                                             | Top-k can over-concentrate on near-duplicates                                                                   |
| Provenance weighting | Evidence and provenance are returned optionally, but not scored                             | High-quality evidence does not improve rank                                                                     |

### Policy wiring gap

The docs say `activate/search` read `retrieval.*` from policy (`docs/mcp-tools.md:17`, `docs/boundary-policy.md:110-114`, `docs/activation-ranking.md:15-18`). The runtime does not currently do that:

- `PolicyDocument` supports `retrieval` (`packages/pce-policy-schemas/src/types.ts:20-34`)
- `defaultPolicy` defines retrieval defaults (`packages/pce-policy-schemas/src/defaults.ts:23-31`)
- runtime state stores only `BoundaryPolicy` (`apps/pce-memory/src/state/memoryState.ts:23-37`)
- `savePolicy` persists only `BoundaryPolicy` JSON (`apps/pce-memory/src/store/policy.ts:16-21`, `apps/pce-memory/src/store/policy.ts:38-52`)
- `handleActivate` uses `getPolicy()` only for boundary filtering (`apps/pce-memory/src/core/handlers.ts:924-931`)

This is a meaningful implementation gap, not just a documentation mismatch.

## 6. Gaps And Recommendations

### Main gaps

1. Retrieval is pooled across selected scopes, so layer distinctions are weak after admission.
2. Boundary filtering is post-ranking, so allowed recall can be underfilled.
3. `kind` only affects recency; `memory_type` does not exist.
4. Intent is present in prompts and validation tasks, but not in the retrieval API.
5. The text branch is critic-ranked rather than lexical-strength-ranked.
6. Policy retrieval settings are documented but not wired into runtime.
7. Active-context persistence is too thin for later analysis because item-level metadata is discarded.

### Recommended retrieval planner

Recommend a **layer-aware, type-aware, intent-aware planner** with this shape:

1. Pre-filter by boundary, layer, and optional type filters before candidate generation.
2. Generate candidates per layer.
3. Apply layer-local scoring profiles.
4. Merge with intent-specific quotas and tie-break rules.
5. Persist active-context items with score breakdown and selection reason.

### Incremental path from current code

| Phase | Change                                                                                                       | Why this order                                                             |
| ----- | ------------------------------------------------------------------------------------------------------------ | -------------------------------------------------------------------------- |
| 1     | Move boundary filtering into candidate generation and add server-side `kind[]` filters                       | Fixes the highest-noise issues without large schema change                 |
| 2     | Wire policy `retrieval.*` into runtime config and replace fixed constants                                    | Makes validation experiments reproducible and tunable                      |
| 3     | Add `memory_type` to claims and retrieval contracts                                                          | Enables real type-aware planning                                           |
| 4     | Add `intent` to `activate` and implement per-layer candidate generation using current `scope` as layer proxy | Delivers layer/type/intent-aware retrieval before full v2 storage redesign |
| 5     | Split active-context persistence into `active_contexts` plus `active_context_items`                          | Preserves evidence for later validation and feedback                       |

### API direction

#### `activate`

Make `activate` the task-facing planner API:

- add `intent`
- add `include_layers`
- add optional `kind_filter` and `memory_type_filter`
- return `source_layer`, `score_breakdown`, `selection_reason`, and item-level provenance summary

#### `search`

Keep `search` as a diagnostic and validation API:

- expose raw candidate sets or breakdowns per layer
- allow exact filters for `scope`, `kind`, `memory_type`, and boundary
- support evaluation workflows that compare planner variants

### Recommendation summary

The current implementation is **scope-aware and partially kind-aware**, but it is **not layer-aware, type-aware, or intent-aware in the sense required by Issue #55**. The best next move is not to add more heuristics to one pooled ranker. It is to turn `activate` into a planner that:

- treats `scope` as a temporary layer proxy
- filters by boundary and type before scoring
- scores each layer differently
- merges results according to intent

That gives the repository a concrete validation target that is compatible with the current codebase and converges cleanly toward the v2 architecture in Issue #49.

## Evidence

- `apps/pce-memory/src/core/handlers.ts:875-931`
- `apps/pce-memory/src/core/handlers.ts:2779-2806`
- `apps/pce-memory/src/core/handlers.ts:2095-2104`
- `apps/pce-memory/src/core/handlers.ts:2440-2462`
- `apps/pce-memory/src/store/hybridSearch.ts:274-365`
- `apps/pce-memory/src/store/hybridSearch.ts:379-443`
- `apps/pce-memory/src/store/hybridSearch.ts:523-674`
- `apps/pce-memory/src/store/hybridSearch.ts:701-949`
- `apps/pce-memory/src/store/rerank.ts:11-18`
- `apps/pce-memory/src/store/rerank.ts:98-148`
- `apps/pce-memory/src/store/claims.ts:24-40`
- `apps/pce-memory/src/store/activeContext.ts:5-16`
- `apps/pce-memory/src/store/policy.ts:16-52`
- `apps/pce-memory/src/db/schema.sql:2-27`
- `apps/pce-memory/src/state/memoryState.ts:23-37`
- `apps/pce-memory/src/domain/types.ts:1-22`
- `apps/pce-memory/test/activate-boundary-filter.test.ts:20-72`
- `apps/pce-memory/test/gRerank.integration.test.ts:144-154`
- `docs/core-types.md:148-154`
- `docs/activation-ranking.md:21-45`
- `docs/activation-ranking.md:72-130`
- `docs/mcp-tools.md:17`
- `docs/boundary-policy.md:110-114`
- `validation/rubric.md:129-145`
- `docs/local-validation-ollama.md:139-175`
- `validation/analysis/memory-layer-storage.md:13-54`
- `validation/analysis/memory-type-taxonomy.md:51-60`
- `validation/analysis/memory-type-taxonomy.md:118-170`

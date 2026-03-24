# pce-memory Vision

> **One-Line Declaration**
> A self-hostable process memory infrastructure for humans and agents that keeps raw observations
> local, distills durable knowledge deliberately, and activates the right context under explicit
> boundaries.

---

## Why Now

1. Stateless AI still reconstructs intent, context, and commitments from scratch in every session.
2. Shared memory without strong boundaries quickly turns into leakage, contamination, and drift.
3. Development work spans multiple tempos:
   sessions move fast, project knowledge settles slower, and norms change slowest.
4. The old scope-centric model is useful for bootstrapping, but it is not strong enough to govern
   promotion, retrieval, and rollback at those different tempos.

---

## Mission

> Visualize the circulation of process and context, and make learning loops reproducible across
> development and operational environments.

---

## Vision

`pce-memory` is built around three memory layers and one explicit lifecycle:

- **Micro**: raw observations, evidence, and active working context
- **Meso**: durable project knowledge and reusable procedures
- **Macro**: reviewed principles, invariants, and policy-adjacent norms

The governing lifecycle is:

`observe -> distill -> promote -> activate(intent) -> feedback -> rollback`

This architecture is designed to make three things true at the same time:

1. **Memory stays useful** because raw task residue does not silently become canonical knowledge.
2. **Memory stays safe** because boundaries are checked before ranking and before promotion.
3. **Memory stays governable** because durable changes have lineage, review state, and rollback.

This document describes the **target v2 architecture**. The current runtime and the v0.1 tool
spec still expose legacy surfaces such as `pce_memory_upsert` and
`observe.extract.single_claim_v0` until the migration plan in the v2 ADR is complete.

---

## Tenets

1. **Boundary-First**: filter by boundary before retrieval and before promotion.
2. **Promotion Is Compilation**: durable memory must be distilled from source material, never
   copied raw by default.
3. **Separate Layer From Type**: layer answers "how durable and governable is this memory";
   memory type answers "what kind of knowledge is this".
4. **Intent-Aware Activation**: activation is a planner, not a pooled search endpoint.
5. **Provenance-by-Default**: durable memory and recalled context must keep evidence and lineage.
6. **Rollback Is First-Class**: repair is append-only and traceable.
7. **Minimal Capture**: remember minimally, and keep raw material local unless promotion is
   justified.
8. **Self-Hostable and Portable**: local-first operation, portable from DuckDB to future
   Postgres/pgvector deployment.

---

## Layer Model

| Layer | Role                                                   | Data shape                         | Sync posture          | Default lifetime |
| ----- | ------------------------------------------------------ | ---------------------------------- | --------------------- | ---------------- |
| Micro | observation, evidence, active context, live task state | raw and volatile                   | never sync by default | hours to days    |
| Meso  | reusable project memory                                | durable and evidence-backed        | default sync surface  | project-scale    |
| Macro | reviewed norms and principles                          | append-only or separately governed | explicit review only  | until superseded |

### Semantic memory types

The v2 model keeps the coarse compatibility layer:

- `kind = fact | preference | task | policy_hint`

And adds the semantic control plane:

- `memory_type = evidence | working_state | knowledge | procedure | norm`

Only micro artifacts use `evidence` as a first-class memory type. Durable meso and macro memory
should use `working_state`, `knowledge`, `procedure`, or `norm`.

This separation lets retrieval and promotion behave differently for:

- evidence that should remain citeable and recent
- working state that should age quickly
- durable knowledge that benefits from hybrid search and critic signals
- procedures that depend on lexical command and trigger matching
- norms that should be deterministically included as guardrails

---

## Problems We Solve

| Problem                 | Failure mode                                        | v2 answer                                      |
| ----------------------- | --------------------------------------------------- | ---------------------------------------------- |
| Context restart cost    | agents repeatedly rediscover local state            | activate an intent-specific active context     |
| Knowledge contamination | local task residue becomes durable memory           | require distill and promotion review           |
| Policy drift            | norms compete with task notes in one flat ranker    | give macro memory separate retrieval semantics |
| Boundary leakage        | disallowed claims consume retrieval budget          | pre-filter by boundary before ranking          |
| Weak auditability       | durable facts lack explicit lineage and repair path | persist promotion queue and rollback ancestry  |

---

## Product Pillars

1. **Observation and Working Set**
   - Capture micro artifacts in `observations` and active-context storage with TTL and scrub-on-expiry.

2. **Distillation and Promotion Governance**
   - Use an explicit promotion queue so durable knowledge is reviewed, evidence-backed, and
     rollbackable.

3. **Layer-Aware Retrieval**
   - Treat activation as a planner that combines per-layer candidate generation with intent-aware
     merge rules.

4. **Boundary and Policy Engine**
   - Apply boundary policy before capture, before promotion, and before retrieval composition.

5. **Critic and Feedback**
   - Update utility, confidence, and freshness from helpful or harmful usage signals.

6. **Portability and Sync**
   - Keep micro local, sync meso by default, and gate macro sync behind explicit review.

---

## MCP-First API

The initial distribution remains MCP-first so IDE agents and local tools share the same memory
surface.

### Core v2 tools

| Tool                           | Role                                       | Notes                                        |
| ------------------------------ | ------------------------------------------ | -------------------------------------------- |
| `pce_memory_observe`           | capture raw micro artifacts                | no durable inline claim creation             |
| `pce_memory_distill`           | create a reviewable promotion candidate    | records lineage, boundary checks, and status |
| `pce_memory_promote`           | create durable meso or macro memory        | provenance required                          |
| `pce_memory_activate`          | compose active context for a task intent   | intent-aware planner API                     |
| `pce_memory_feedback`          | send usefulness and correctness signals    | feeds critic and future ranking              |
| `pce_memory_rollback`          | supersede or repair invalid durable memory | append-only                                  |
| `pce_memory_boundary_validate` | evaluate boundary handling                 | shared safety primitive                      |
| `pce_memory_policy_apply`      | update policy                              | governance channel                           |

### Supporting API posture

- `search` may remain as a diagnostic or evaluation interface.
- direct `upsert` is no longer the primary workflow and should be treated as a narrowly scoped
  escape hatch for already-distilled durable knowledge.

### Representative flow

1. `observe` captures raw material into micro storage.
2. `distill` turns observations, claims, or active context into a promotion candidate.
3. `promote` writes accepted knowledge into meso or macro memory.
4. `activate(intent)` builds a short-lived active context for a concrete task.
5. `feedback` updates critic signals after use.
6. `rollback` repairs durable memory when a promoted item is later invalidated.

---

## Activate Planner

`activate` should be planner-shaped rather than search-shaped.

### Input

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

### Planner outline

1. pre-filter by boundary, layer, and optional type filters
2. generate candidates per layer
3. score each layer with layer-local and type-local rules
4. merge with intent-specific quotas and tie-break rules
5. persist `active_contexts` and `active_context_items` with score breakdown and selection reason

### Intent profiles

| Intent            | Layer mix            | Type mix                                      | Special behavior                                         |
| ----------------- | -------------------- | --------------------------------------------- | -------------------------------------------------------- |
| `resume_task`     | micro > meso > macro | `working_state`, `task`, relevant `knowledge` | prioritize freshness and issue or branch affinity        |
| `debug_incident`  | micro + meso         | `evidence`, `knowledge`, `procedure`          | prioritize error-token lexical match and recent evidence |
| `design_decision` | meso + macro         | `knowledge`, `procedure`, `norm`              | prioritize evidence density and stable constraints       |
| `policy_check`    | macro > meso         | `norm`, `policy_hint`, supporting `knowledge` | deterministic guardrail prepend and fail-closed bias     |

---

## Data Model Direction

### Micro

- `observations`
- `evidence`
- `active_contexts`
- `active_context_items`

Micro memory is volatile, boundary-sensitive, and not part of default sync.

### Durable memory

- meso durable project memory
- macro principle catalog
- `evidence` remains micro-only and is linked into durable memory through evidence refs

The first implementation may still share one DuckDB file, but durable memory should not remain one
flat pooled corpus.

### Promotion queue

The promotion queue is mandatory because it stores:

- source lineage
- proposed kind and memory type
- target layer
- boundary and policy checks
- acceptance or rejection state
- reviewer metadata
- rollback ancestry

---

## Governance Rules

1. No public write API creates durable canonical `session` memory.
2. No raw observation is promoted directly into durable memory.
3. Macro memory is not written ad hoc from observation input.
4. `secret` content is never silently promoted.
5. Boundary class can upgrade, never downgrade.
6. Rollback records supersession instead of mutating durable history in place.

---

## Stakeholder Value

- **Developers** get faster task resumption without polluting project memory with local residue.
- **Teams** get a reusable project knowledge base with clearer procedures and postmortem lineage.
- **Organizations** get boundary-first AI memory with explicit policy and principle handling.
- **Researchers and operators** get inspectable promotion, activation, and rollback records.

---

## Success Measures

- boundary compliance rate
- provenance coverage rate
- time to useful activation
- candidate-to-promotion latency
- rollback MTTR
- critic convergence by memory type

The v2 architecture adds one new measure that matters operationally:

- **promotion review throughput**: how quickly a good candidate moves from micro evidence into
  durable meso or macro memory without bypassing governance

---

## Roadmap Direction

- **v2 architecture cutover**: promotion queue, memory types, active-context enrichment, and
  intent-aware activation
- **retrieval policy wiring**: runtime support for `retrieval.*` policy controls
- **macro governance**: reviewed principle promotion and rollback workflows
- **portability**: Postgres/pgvector and broader sync strategies after the v2 lifecycle is stable

---

## Non-Goals

- centralized SaaS lock-in
- direct raw-observation sync
- black-box memory without provenance
- durable session memory as a default user-facing feature
- one flat retrieval model for every task intent

---

## Trust and Safety

- redact before send
- least privilege by boundary
- fail closed when policy is missing
- show provenance, boundary, and policy metadata with durable memory and activation results

### Threat model

| Threat                             | Failure mode                                 | Countermeasure                                                    |
| ---------------------------------- | -------------------------------------------- | ----------------------------------------------------------------- |
| Cross-boundary recall              | disallowed memory enters active context      | pre-filter by boundary before candidate generation                |
| Memory contamination               | tentative evidence becomes durable knowledge | require distill and promotion review                              |
| Prompt injection via recalled text | unsafe fragments shape generation            | cite sources, keep provenance, and preserve layer metadata        |
| Policy drift                       | macro norms lose authority in pooled ranking | retrieve macro memory with deterministic or quota-based inclusion |

---

## Story

A coding agent debugging a production issue should not receive one flat pile of "session/project/
principle" claims. It should receive:

1. fresh evidence from the current incident
2. relevant project knowledge and procedures
3. required norms and policies

That is the point of the v2 redesign:

- micro stays local and recent
- meso stays reusable and durable
- macro stays authoritative and governable

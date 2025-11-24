# pce-memory Vision

> **One-Line Declaration**
> A **self-hostable process memory infrastructure** that enables humans and agents to share **context** under **boundaries**, continuously learning through **inscription** and **critic** mechanisms.

---

## Why Now

1. **Limitations of Stateless AI**  LLMs infer from scratch each time, unable to maintain continuous context, commitments, or provenance.
2. **Context Drift and Leakage Risks**  As context expands, **off-purpose usage** and **confidentiality breaches** become more likely.
3. **Pace Layering Disconnection**  The update tempos of sessions (fast), team procedures (medium), and institutions (slow) don't align, resulting in **knowledge that never settles or becomes frozen**.

**pce-memory** implements the PCE (Process-Context Engine) principles through:

- **Latent Context Pool (LCP)** and
- **Active Context (AC)**,
- **Boundaries and Invariants**,
- **Inscription and Provenance**,
- **Critic and Success Bundles**
to realize **"safely remember, quickly forget, and correctly recall as needed."**

---

## Mission

> **Visualize the circulation of process and context, embedding reproducible learning loops into every development and operational environment.**

---

## Vision

- **Sovereign Memory**: Not exclusively dependent on SaaS; operable **locally/on-premises** with a **boundary-first** approach.
- **Memory as Relationship**: Meaning is not a fixed object but a **function**. It evolves through LCP”AC circulation, translation, mediation, and inscription.
- **Pace-Aligned Memory**: **Distill** from session (fast) ’ procedures (medium) ’ institutions (slow). In case of incidents, **rollback** (settle down).
- **Revocable and Visible Memory**: Provenance is always traceable and **can be revoked at any time**. Errors are capitalized and recovered into learning.
- **Coexistence Memory**: Humans, agents, and institutions collaborate under **the same boundary**, where **dangers are stopped in early stages and benefits are promoted to later stages**.

---

## Tenets

1. **Boundary-First**: Determine **allow/edit/deny** upfront based on purpose, confidentiality, and provenance.
2. **Provenance-by-Default**: All recalls come with evidence and pathways.
3. **LCP/AC Dual-Phase**: Separate latent (long-term) and active (short-term), cycling through **selection ’ interpretation ’ evaluation ’ distillation**.
4. **Pace-Aware**: Establish **promotion/rollback** procedures aligned with update tempo (fast/medium/slow).
5. **Critic-in-the-Loop**: Continuously update **utility, confidence, and reproducibility** through explicit/implicit feedback.
6. **Interoperable**: Connect with IDEs and agents via CLI/HTTP/MCP.
7. **Self-Hostable & Portable**: **Portable** from DuckDB ’ Postgres/pgvector. Switchable embeddings between **OpenAI + local**.
8. **Minimal Capture**: **Remember minimally, don't over-remember**. Staged as Observation ’ Claim ’ Graph.
9. **Explainable Retrieval**: Hybrid search (Dense + BM25) + re-ranking (quality, trust, recency).
10. **Ethics & Safety**: Block PII/Secrets at boundaries with strict **Redact-before-Send**.

---

## Problems We Solve (Problems ’ Outcomes)

| Problem | Details | pce-memory Solution | Target Outcome |
|---|---|---|---|
| Lack of Context Continuity | Loss of prerequisites when resuming tasks | LCP’AC selection `r(q,C^L,B,policy)` | Reduced restart time |
| Leakage & Off-Purpose Use | PII/confidential info mixed into recall | Boundary pre-filter + Redact | Virtually zero unauthorized recalls |
| Knowledge Freeze/Drift | Changes don't settle or become rigid | Pace-aware distillation/rollback | Healthy evolution of procedures |
| Lack of Reproducibility | Can't answer "why this solution" | Provenance + Inscription | Auditable decision-making |
| Feedback Failure | Learning doesn't accumulate | Critic + Success Bundles | Normalized continuous improvement |

---

## Product Pillars

1. **Memory Core (LCP/AC)**
   - Observation ’ Claim ’ Graph. Accumulate in LCP **with provenance**, select and summarize AC query-adaptively.
2. **Boundary Engine**
   - Invariants, pre/post-conditions, purpose tags. Define **Gate / Translate / Mediate**.
3. **Retrieval & Activation**
   - Hybrid search + re-ranking. Compose AC via **`r(q,C^L,B,policy)`**.
4. **Critic & Telemetry**
   - Update **utility/confidence/recency** via helpful/harmful/outdated/duplicate + adoption logs.
5. **Inscription & Governance**
   - Audit logs, version control, diffs. **Distill/rollback** procedures.
6. **SDK / CLI / MCP**
   - Unified I/F callable from Codex/Claude Code/Cursor for **search / upsert / feedback**.

---

## MCP-first (MVP): Function Provision to Agents

> The initial distribution format is **tool provision to agents** via **MCP (Model Context Protocol)**. Top priority is immediate usability from IDE/code assistants (Codex / Claude Code / Cursor, etc.).

### Provided Tools (Minimal)

| Tool Name | Input (req) | Output (resp) | Purpose |
|---|---|---|---|
| `pce.memory.search` | `{ query, top_k?, scope?, allow? }` | `[{ claim, scores, evidences, policy_version }]` | Recall known prerequisites, conventions, prohibitions |
| `pce.memory.activate` | `{ q, scope?, allow? }` | `{ active_context_id, claims[] }` | Compose AC from LCP (r function) |
| `pce.memory.upsert` | `{ text, kind?, scope?, boundary_class?, entities?, relations?, provenance? }` | `{ id }` | Register important fragments (Observation/Claim/Graph) |
| `pce.memory.feedback` | `{ claim_id, signal: helpful|harmful|outdated|duplicate, score? }` | `{ ok: true }` | Evaluation loop via Critic |
| `pce.memory.boundary.validate` | `{ payload, allow?, scope? }` | `{ allowed, reason, redacted? }` | Boundary check before generation / Redact-before-Send |
| `pce.memory.policy.apply` | `{ yaml }` | `{ version }` | Apply policy (invariants, purpose tags) |

> All tools include **Provenance** and **policy_version** in responses to ensure auditability.

### Representative Flow (Agent Side)

1. **Activation**: Get AC via `pce.memory.activate` and attach to prompt header (prerequisite injection).
2. **Generation**: Check with `pce.memory.boundary.validate` before generating candidates (redact if needed).
3. **Upsert**: Save decisions and design rationale via `pce.memory.upsert`. Provenance (commit/URL) mandatory.
4. **Feedback**: Return adoption/rejection results via `pce.memory.feedback` for next re-ranking.

### AC Generation Function r Outline (Pseudo)

> AC = r(q, C^L, B, policy, critic)

1) **Boundary Pre-filter**: Narrow LCP by `scope/allow/invariants`
2) **Search**: `S = ± * dense + ² * BM25` (hybrid)
3) **Re-rank**: `S' = S * g(utility, confidence, recency)` (critic reflection)
4) **Redact**: Block confidential info per boundary (attach Provenance)
5) **Compose**: Return top k as AC (issue `active_context_id`)

### Safety Design

- **Boundary-First**: Always call `validate` before/after generation. Pre-filter with `scope/allow` during recall.
- **Redact-before-Send**: Auto-mask PII/Secrets within MCP tools. Transmission logs attached to Provenance.
- **Fail-closed**: No permission when policy unloaded; return reason and action (`policy.apply`).

### MCP Tool Quality Characteristics (Mini-Spec)

| Tool | Idempotency | Timeout | Payload | Errors (Example) | Notes |
|---|---:|---:|---:|---|---|
| search | safe (GET-like) | 10s | 32KB | BOUNDARY_DENIED / RATE_LIMIT | With citations, read-only |
| activate | safe | 15s | 16KB | POLICY_MISSING / INVALID_SCOPE | AC ID and composition list |
| upsert | idempotent via `content_hash` | 10s | 64KB | DUPLICATE / INVALID_BOUNDARY | Provenance required (commit/URL) |
| feedback | idempotent via `(claim_id, ts bucket)` | 3s | 4KB | UNKNOWN_CLAIM | Aggregated to critic |
| boundary.validate | safe | 5s | 32KB | BOUNDARY_DENIED | Returns redact result |
| policy.apply | non-idempotent (versioned) | 10s | 128KB | UNAUTHORIZED | GitOps approval recommended |

### MVP Targets

- IDE: **Cursor / VS Code** (extension)
- Agents: **Codex / Claude Code** (standardize search / upsert / feedback via MCP)

> Future: HTTP/CLI provided as wrappers of MCP implementation. Prioritize MCP as core I/F first to minimize agent integration friction.

---

## Definitions & Qualities

- **Critic**: An evaluator (two-phase: pre-guard / post-evaluation) that ingests adoption/rejection/correction signals and updates `utility/confidence/recency`.
- **Success Bundle**: A metric bundle of { coherence, portability, counterfactual robustness, performative success, revocability, traceability, reproducibility }.
- **Distill**: Procedure to promote AC achievements to LCP (mandatory deduplication, provenance attachment, boundary alignment).
- **Rollback**: Procedure to revert LCP to safe side when errors or boundary violations are discovered (explicitly show impact scope and provenance).
- **Invariants**: Core invariants of boundaries. Fail-closed on violation; exceptions granted only through manual review.

---

## Stakeholder Value

- **Individual Developers**: Fast task resumption. IDE agents **read prerequisites first**.
- **Teams**: Decisions are documented; **incident recurrence prevention knowledge** auto-promoted.
- **Organizations**: **Safe AI utilization** compliant with norms/institutions (slow layer).
- **Researchers**: Increased **reproducibility** via provenance and versioning.

---

## Success Bundles (North Star & KPIs)

- **Boundary Compliance Rate** (unauthorized recall rate H 0)
- **Provenance Coverage Rate** (rate of responses with provenance links)
- **TTR (Time-to-Retrieval)** (time to useful recall)
- **Distillation Half-Life** (average cycle time for AC’LCP promotion)
- **Rollback MTTR** (time from error detection to rollback)
- **Critic Convergence** (stability of utility/confidence)

### KPI Measurement Formulas (Examples)

- **Boundary Compliance Rate (14-day moving window)**
  = 1  (unauthorized recalls / total recalls)
- **Provenance Coverage Rate (14 days)**
  = responses with valid provenance links / total responses
- **TTR p90 (14 days)**
  = 90th percentile time to one useful recall (feedback=helpful)
- **Distillation Half-Life (30 days)**
  = median time (days) from AC to LCP promotion
- **Rollback MTTR (30 days)**
  = average time from "error detection" to "LCP repair"
- **Critic Convergence (30 days)**
  = weekly change rate of Var(utility) (“ stabilization is good)

---

## Roadmap (Themes)

- **v0.1**: Single-node Core (DuckDB), LCP/AC, basic Boundary, CLI/MCP
- **v0.2**: Graph memory, Re-rank, Critic/Telemetry, Provenance enhancement
- **v0.3**: Pace-aware distillation/rollback, Boundary UI, audit view
- **v0.4**: Postgres/pgvector, organizational operations, template policies, connectors
- **v1.0**: Operational foundation (SLO/SLA), audit trails, ecosystem release

---

## Non-Goals

- Centralized SaaS lock-in
- Full replacement as agent orchestrator
- Capture for capture's sake (**over-capture**)
- Black-box memory without provenance

---

## Trust & Safety

- **Redact-before-Send**, **least privilege**, **data minimization**
- Block PII/Secrets via `boundary_class`, **escalate to manual review**
- Transparency: Always present **provenance, boundary, policy**

## Threat Model (Minimal)

| Threat | Description | Countermeasure |
|---|---|---|
| Cross-boundary Recall | Fragments outside boundary mixed into AC | boundary.validate pre-filter / allowlist / fail-closed |
| Prompt Injection | Recalled fragments contaminate generation system | Citations mandatory, dangerous token blocking, sandbox indication |
| PII/Secret Leakage | Confidential info sent to external APIs | Redact-before-Send / scope-based blocking |
| Duplication/Conflict | Upsert resend/conflict | content_hash / CRDT strategy / manual review |
| Audit Failure | Missing provenance or policy_version | Provenance mandatory, append-only logs |

---

## Story (60-Second Scenario)

> In the morning, when you open your IDE, pce-memory presents **yesterday's decisions**, **related designs**, and **prohibitions** at the top.
> Generated proposals pass through **boundaries**, with dangers blocked early. Adopted fragments are **distilled** overnight
> and **promoted** to team conventions. Failures are **rolled back with provenance**, preventing recurrence.

---

## Call to Action

- **Starting Today**: Enable LCP/AC + Boundary in personal projects, completing one **prerequisite ’ proposal ’ distillation** cycle.
- **This Month**: Articulate just 5 team **invariants** (constraints to protect) and embed them in Boundary.
- **This Quarter**: Establish **promotion/rollback** operations with Critic and audit view.

## Implementation Runbook (30-60-90)

- **Day 0-30**: Minimal Boundary set (5 invariants) / Connect MCP search+validate to IDE / Baseline KPIs
- **Day 31-60**: Enable feedback’critic / Start manual review operations for distill / Test Redact-before-Send
- **Day 61-90**: Rollback procedure drills / Set pace-aware promotion SLO / Publish audit view

---

### Terminology (Excerpt)

- **LCP**: Latent Context Pool (long-term relational memory)
- **AC**: Active Context (short-term working set)
- **Boundary / Invariants**: Purpose, confidentiality, invariants
- **Inscription / Provenance**: Inscription, provenance
- **Critic / Success Bundle**: Critic, success bundle

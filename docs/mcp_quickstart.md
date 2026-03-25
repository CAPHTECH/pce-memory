# MCP Quickstart — pce-memory v2

> Goal: call `pce-memory` over MCP from Claude Code / Codex / Cursor and run the current v2 flow once.
>
> Recommended flow:
> `policy_apply -> observe -> distill -> promote -> activate -> boundary_validate -> feedback`

## 1. Connect the MCP server

Usually the client starts the server on demand over stdio.

Example `.mcp.json`:

```json
{
  "mcpServers": {
    "pce-memory": {
      "command": "npx",
      "args": ["-y", "pce-memory"],
      "env": {
        "PCE_DB": "~/.pce/your-project.db"
      }
    }
  }
}
```

If the client can list `pce_memory_*` tools, the connection is working.

## 2. State gate

Before the first non-state call in a session:

1. Call `pce_memory_state`
2. If the state is `Uninitialized`, call `pce_memory_policy_apply`
3. Then continue with `observe`, `distill`, `promote`, `activate`, and `feedback`

Notes:

- `observe` is raw-only. It does not create durable claims inline.
- Durable memory should normally go through `observe -> distill -> promote`.
- `pce_memory_upsert` is the escape hatch for already-distilled durable knowledge.
- `pce_memory_upsert` rejects `scope: "session"` and `boundary_class: "secret"`.

## 3. E2E example

### 3.1 `pce_memory_policy_apply`

```json
{
  "yaml": "version: 0.1\nscopes:\n  session: { ttl: '7d' }\n  project: { ttl: '120d' }\n  principle: { ttl: 'inf' }\nboundary_classes:\n  public: { allow: ['*'] }\n  internal: { allow: ['answer:task', 'tool:*'] }\n  pii: { allow: ['tool:contact-lookup'], redact: ['email', 'phone'], escalation: 'human_review' }\n  secret: { allow: [], escalation: 'deny' }\n"
}
```

### 3.2 `pce_memory_observe`

Capture raw evidence or a decision memo.

```json
{
  "source_type": "chat",
  "content": "Cancellation API returns 202 and remains idempotent for repeated requests.",
  "boundary_class": "internal",
  "tags": ["feature:billing", "decision-draft"]
}
```

Expected result: `observation_id` such as `obs_...`

### 3.3 `pce_memory_distill`

Create a reviewable candidate from the raw observation.

```json
{
  "source_observation_ids": ["obs_..."],
  "proposed_kind": "fact",
  "proposed_scope": "project",
  "proposed_memory_type": "knowledge"
}
```

Expected result: `candidate_id` such as `pq_...`

### 3.4 `pce_memory_promote`

Promote the candidate into durable memory.

```json
{
  "candidate_id": "pq_...",
  "provenance": {
    "at": "2026-03-24T00:00:00Z",
    "actor": "claude"
  }
}
```

Expected result: `claim_id` such as `clm_...`

### 3.5 `pce_memory_activate`

Recall relevant durable knowledge for the task.

```json
{
  "q": "cancellation API idempotent 202 response",
  "scope": ["project"],
  "allow": ["answer:task"],
  "intent": "design_decision",
  "kind_filter": ["fact", "preference", "policy_hint"],
  "memory_type_filter": ["knowledge", "procedure", "norm"],
  "top_k": 10
}
```

Expected result: `active_context_id` and ranked `claims[]`

### 3.6 `pce_memory_boundary_validate`

Validate output before reusing or sending it.

```json
{
  "payload": "Contact billing-team@example.com for cancellation escalations.",
  "allow": ["answer:task"],
  "scope": "project"
}
```

### 3.7 `pce_memory_feedback`

Send feedback after using an activated durable claim.

```json
{
  "claim_id": "clm_...",
  "signal": "helpful",
  "score": 1
}
```

## 4. When to use `upsert`

Use `pce_memory_upsert` only when the knowledge is already distilled and you do not need a reviewable promotion step.

Good examples:

- confirmed architecture decisions
- reviewed coding conventions
- stable project procedures

Do not use `upsert` for:

- session work in progress
- raw logs or temporary notes
- secrets

## 5. Common mistakes

| Mistake                                           | What to do instead                                     |
| ------------------------------------------------- | ------------------------------------------------------ |
| Writing session state with `upsert`               | Use `observe`                                          |
| Writing secrets with `upsert`                     | Use `observe` and keep it non-durable                  |
| Skipping `distill` and `promote` for raw findings | Use the full v2 path                                   |
| Sending `feedback` for an observation ID          | Send feedback for a durable `claim_id` from `activate` |
| Using vague English like `"auth"`                 | Use concrete queries like `"JWT refresh token expiry"` |

## 6. Current tool surface

The current server exposes these tool groups:

- lifecycle: `pce_memory_state`, `pce_memory_policy_apply`, `pce_memory_health`
- raw capture: `pce_memory_observe`
- durable write path: `pce_memory_distill`, `pce_memory_promote`, `pce_memory_rollback`
- durable escape hatch: `pce_memory_upsert`
- recall and safety: `pce_memory_activate`, `pce_memory_boundary_validate`, `pce_memory_feedback`
- graph and sync: `pce_memory_upsert_entity`, `pce_memory_upsert_relation`, `pce_memory_sync_*`

For the exact server surface, prefer `ListTools` output or `apps/pce-memory/src/core/handlers.ts`.

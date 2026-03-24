# pce-memory

PCE Memory is the MCP server implementation of Process-Context Engine (PCE).

## MCP Configuration

Use a per-project database path.

### Claude Code

Add this to `.mcp.json`:

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

### Claude Desktop

Add the same server to `~/Library/Application Support/Claude/claude_desktop_config.json`.

### Cline / Roo Code

Register the same stdio server in `settings.json`.

## Quick Start

```bash
# run directly
npx pce-memory

# or install globally
npm install -g pce-memory
pce-memory
```

## Recommended v2 workflow

The current write path is:

```text
observe -> distill -> promote -> activate(intent) -> feedback -> rollback
```

Rules:

- `observe` is raw-only and does not create durable claims inline.
- `upsert` is only for already-distilled durable knowledge.
- `upsert` rejects `scope: "session"` and `boundary_class: "secret"`.
- use `activate` as the task-facing recall API.
- send `feedback` for durable `claim_id`s that were actually used.

## Core tools

### `pce_memory_policy_apply`

Initialize the policy and state machine.

```ts
{ yaml?: string }
```

### `pce_memory_observe`

Store raw session evidence with TTL.

```ts
{
  source_type: "chat" | "tool" | "file" | "http" | "system",
  content: string,
  boundary_class?: "public" | "internal" | "pii" | "secret",
  tags?: string[],
  ttl_days?: number
}
```

### `pce_memory_distill`

Create a promotion candidate from observations, claims, or an active context.

```ts
{
  source_observation_ids?: string[],
  source_claim_ids?: string[],
  active_context_id?: string,
  proposed_kind?: "fact" | "preference" | "task" | "policy_hint",
  proposed_scope?: "project" | "principle",
  proposed_memory_type?: "working_state" | "knowledge" | "procedure" | "norm",
  note?: string
}
```

### `pce_memory_promote`

Promote a pending candidate into durable memory.

```ts
{
  candidate_id: string,
  provenance: {
    at: string,
    actor?: string
  },
  reviewers?: string[],
  review_note?: string
}
```

### `pce_memory_activate`

Recall task-relevant knowledge.

```ts
{
  q?: string,
  scope: ("session" | "project" | "principle")[],
  allow: string[],
  intent?: "resume_task" | "debug_incident" | "design_decision" | "policy_check",
  kind_filter?: ("fact" | "preference" | "task" | "policy_hint")[],
  memory_type_filter?: ("working_state" | "knowledge" | "procedure" | "norm" | "evidence")[],
  include_observations?: boolean,
  top_k?: number
}
```

### `pce_memory_upsert`

Escape hatch for already-distilled durable knowledge.

```ts
{
  text: string,
  kind: "fact" | "preference" | "task" | "policy_hint",
  scope: "project" | "principle",
  boundary_class: "public" | "internal" | "pii",
  memory_type?: "working_state" | "knowledge" | "procedure" | "norm" | "evidence",
  provenance: {
    at: string,
    actor?: string
  },
  content_hash?: string
}
```

### `pce_memory_rollback`

Append-only repair for invalid durable claims.

```ts
{
  claim_id: string,
  reason: string,
  provenance: {
    at: string,
    actor?: string
  }
}
```

### `pce_memory_boundary_validate`

Validate and redact text before reuse or output.

```ts
{
  payload: string,
  scope?: string,
  allow?: string[]
}
```

### `pce_memory_feedback`

Record quality feedback for a durable claim.

```ts
{
  claim_id: string,
  signal: "helpful" | "harmful" | "outdated" | "duplicate",
  score?: number
}
```

### `pce_memory_state`

Read the current state machine status.

```ts
{ debug?: boolean }
```

### Other tools

The server also exposes:

- `pce_memory_health`
- `pce_memory_upsert_entity`
- `pce_memory_upsert_relation`
- `pce_memory_query_entity`
- `pce_memory_query_relation`
- `pce_memory_sync_push`
- `pce_memory_sync_pull`
- `pce_memory_sync_status`

## State machine

The server restores and enforces these states:

```text
Uninitialized -> PolicyApplied -> HasClaims -> Ready
```

Notes:

- `observe` can be used after policy initialization and does not create durable claims by itself.
- `activate` becomes available once durable claims exist.
- `feedback` is intended for durable claims that were activated and used.

## Requirements

- Node.js >= 22.18.0

## License

MIT

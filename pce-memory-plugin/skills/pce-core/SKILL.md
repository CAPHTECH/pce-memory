---
name: pce-core
context: fork
description: "Core pce-memory workflow skill for activate/upsert/feedback. Guides knowledge recall, recording, and feedback with proper scope/kind/boundary selection. Triggered by: 'knowledge recall', 'record to memory', 'activate context', 'memory workflow'."
argument-hint: "[activate|upsert|feedback] [query or text...]"
allowed-tools: "mcp__pce-memory__pce_memory_activate, mcp__pce-memory__pce_memory_upsert, mcp__pce-memory__pce_memory_feedback, mcp__pce-memory__pce_memory_state, mcp__pce-memory__pce_memory_policy_apply, mcp__pce-memory__pce_memory_upsert_entity, mcp__pce-memory__pce_memory_upsert_relation"
---

# PCE Core - Knowledge Management Workflow

Manages the core pce-memory workflow: activate → work → upsert → feedback.

## Argument Parsing

Parse `$ARGUMENTS`:
- `activate [query]` → Knowledge recall mode
- `upsert [kind] [text]` → Knowledge recording mode
- `feedback [claim-id] [signal]` → Feedback mode
- No arguments → Full workflow guide

## 1. Knowledge Recall (Activate)

Retrieve relevant knowledge from pce-memory and inject into working context.

### Steps

1. Check current state with `pce_memory_state`
2. If Uninitialized, run `pce_memory_policy_apply` first
3. Call `pce_memory_activate`:
   - `q`: Extract keywords from user intent (natural language OK)
   - `scope`: Select appropriate scope (see [scope-boundary-guide.md](references/scope-boundary-guide.md))
   - `top_k`: Usually 5-10
   - `allow`: Use `["answer:task"]` or `["answer:fact"]` as appropriate
4. Summarize retrieved knowledge and present to user

### Best Practices

- Be specific with queries: "JWT auth token expiry" is better than "auth"
- Combine multiple activates for comprehensive coverage
- Filter by priority when many results are returned

## 2. Knowledge Recording (Upsert)

Persist important decisions and discoveries to pce-memory.

### Steps

1. Identify content worth recording
2. Select appropriate `kind`:
   - `fact`: Architecture decisions, technical constraints, API specs
   - `preference`: Coding style, tool choices, naming conventions
   - `task`: Work in progress, TODO items
   - `policy_hint`: Security requirements, operational rules
3. Determine `scope` and `boundary_class` (see [scope-boundary-guide.md](references/scope-boundary-guide.md))
4. Call `pce_memory_upsert`
5. Optionally update graph with `pce_memory_upsert_entity` / `pce_memory_upsert_relation`

### Best Practices

- Keep text concise and specific (1-2 sentences ideal)
- Always set `content_hash` (SHA256)
- Include `provenance` for traceability
- Be selective: record only important decisions
- Always write in English

## 3. Feedback

Report quality of knowledge retrieved via activate.

### Steps

1. Identify the claim_id from activated knowledge
2. Select appropriate signal:
   - `helpful`: Contributed to problem solving
   - `harmful`: Was incorrect, caused bugs
   - `outdated`: Information is stale
   - `duplicate`: Same content exists in another claim
3. Call `pce_memory_feedback`

## Workflow Patterns

See [workflow-patterns.md](references/workflow-patterns.md).

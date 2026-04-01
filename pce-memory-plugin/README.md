# pce-memory-plugin

Claude Code plugin for persistent knowledge management with [pce-memory](https://github.com/rizumita/pce-memory) MCP server.

## Design Philosophy

AI autonomously operates pce-memory. No manual user interaction required.

- **Auto-bootstrap**: Checks state, initializes, and recalls knowledge at session start
- **Auto-activate**: Detects task-like prompts and recalls relevant knowledge automatically
- **Pre-injected persistence guidance**: Session-start and prompt-submit hooks tell the agent how to persist context before ending, without relying on a stop hook
- **V2 write path guidance**: Durable memory follows `observe -> distill -> promote`, with `upsert` reserved as an escape hatch for already-distilled knowledge
- **Layer-aware recall/sync**: Skills describe micro/meso/macro behavior, memory types, and sync boundaries

## Installation

```bash
claude --plugin-dir ./pce-memory-plugin
```

`.mcp.json` intentionally keeps `npx pce-memory@latest` until the next npm publish updates the package version reference.

## V2 Workflow

The plugin documentation and skills target the pce-memory v2 API:

```text
observe -> distill -> promote -> activate(intent) -> feedback -> rollback
```

- `observe` captures raw micro-memory only. It does not create durable claims inline.
- `distill` creates a reviewable promotion candidate with lineage and proposed `kind` / `memory_type`.
- `promote` turns a pending candidate into meso or macro durable memory with mandatory provenance.
- `activate` remains the task-facing recall API and now supports `intent`, `kind_filter`, `memory_type_filter`, and `include_observations`.
- `rollback` is the append-only repair path for invalid durable memory.
- `upsert` still exists, but only as a narrow escape hatch for already-distilled project/principle knowledge.

## How It Works

### Hooks (fully autonomous)

| Event                    | Behavior                                                            |
| ------------------------ | ------------------------------------------------------------------- |
| SessionStart             | Check state → policy_apply → activate; inject persistence guidance (also fires after compaction) |
| UserPromptSubmit         | Inject base protocol every message + activate on task detection     |
| PostToolUse(Write\|Edit) | Remind the agent to record architecturally significant changes      |

The runtime hooks remain lightweight. The v2 durable-memory contract is documented in the skills so agents can choose `observe`, `distill`, `promote`, `activate(intent)`, `feedback`, and `rollback` correctly.

### Skills (AI internal reference)

- **pce-core**: v2 core workflow, activate planning, and upsert escape hatch
- **pce-promotion**: distill/promote/rollback pipeline guide
- **pce-graph**: Entity and relation management
- **pce-sync**: push/pull/status, memory_type-aware sync, layer-aware export/import rules

### Agent

- **knowledge-curator**: Duplicate detection, staleness check, graph integrity audit

## License

MIT

# pce-memory-plugin

Claude Code plugin for persistent knowledge management with [pce-memory](https://github.com/rizumita/pce-memory) MCP server.

This plugin is the recommended P0 integration path for daily use with Claude Code.

## Design Philosophy

AI autonomously operates pce-memory with a conservative memory policy. No manual user interaction is required for the core loop.

- **Auto-bootstrap**: Checks state, initializes, and recalls knowledge at session start
- **Auto-activate**: Detects task-like prompts and recalls relevant knowledge automatically
- **Auto-record**: Persists only important task state and explicit decisions at session end
- **Auto-observe**: Flags significant file changes as recording candidates, not automatic memory writes

## Installation

```bash
claude --plugin-dir ./pce-memory-plugin
```

The bundled MCP config uses `npx -y pce-memory@latest`.

## How It Works

### P0 Workflow

The plugin fixes the primary workflow to:

1. `state` check
2. `policy_apply` only when uninitialized
3. `activate` before work when claims exist
4. selective `upsert` at session end
5. `feedback` for recalled knowledge that was used

All automatic claims and activate queries are written in English for consistency.

### Hooks (fully autonomous, conservative recording)

| Event | Behavior |
|-------|----------|
| SessionStart | Resolve project DB → state check → policy_apply if needed → activate when claims exist |
| UserPromptSubmit | Inject state guard every message + activate on task detection |
| Stop | Close completed tasks, persist in-progress tasks, record only explicit facts/preferences |
| PostToolUse(Write\|Edit) | Flag architecturally significant file changes as candidates for recording |

### Recording Rules

- Record: in-progress/blocked task state, architecture decisions, API/schema decisions, naming/tooling conventions, bug root causes
- Do not record: minor fixes, obvious repo facts, speculative notes, completed tasks as new task claims, secrets
- Task claims use the format:
  - `TASK [status:in_progress|blocked] <description>. Progress: <...>. Next: <...>. Blockers: <...>.`

### Skills (AI internal reference)

- **pce-core**: activate/upsert/feedback workflow guide
- **pce-graph**: Entity and relation management
- **pce-sync**: push/pull/status, CRDT merge

### Agent

- **knowledge-curator**: Duplicate detection, staleness check, graph integrity audit

## License

MIT

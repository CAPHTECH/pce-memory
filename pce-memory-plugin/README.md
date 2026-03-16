# pce-memory-plugin

Claude Code plugin for persistent knowledge management with [pce-memory](https://github.com/rizumita/pce-memory) MCP server.

## Design Philosophy

AI autonomously operates pce-memory. No manual user interaction required.

- **Auto-bootstrap**: Checks state, initializes, and recalls knowledge at session start
- **Auto-activate**: Detects task-like prompts and recalls relevant knowledge automatically
- **Auto-record**: Records important design decisions automatically; final check at session end
- **Auto-observe**: Records changes to architecturally significant files

## Installation

```bash
claude --plugin-dir ./pce-memory-plugin
```

## How It Works

### Hooks (fully autonomous)

| Event | Behavior |
|-------|----------|
| SessionStart | Check state → policy_apply → activate (also fires after compaction) |
| UserPromptSubmit | Inject base protocol every message + activate on task detection |
| Stop | Auto-record important decisions with upsert |
| PostToolUse(Write\|Edit) | Auto-record on architecturally significant file changes |

### Skills (AI internal reference)

- **pce-core**: activate/upsert/feedback workflow guide
- **pce-graph**: Entity and relation management
- **pce-sync**: push/pull/status, CRDT merge

### Agent

- **knowledge-curator**: Duplicate detection, staleness check, graph integrity audit

## License

MIT

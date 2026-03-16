---
name: pce-sync
context: fork
description: "Team knowledge synchronization skill for pce-memory. Manages push/pull/status with Git hooks integration and CRDT merge. Triggered by: 'sync knowledge', 'push knowledge', 'pull team knowledge', 'check sync status'."
argument-hint: "[push|pull|status]"
allowed-tools: "mcp__pce-memory__pce_memory_sync_push, mcp__pce-memory__pce_memory_sync_pull, mcp__pce-memory__pce_memory_sync_status, mcp__pce-memory__pce_memory_state"
---

# PCE Sync - Team Knowledge Synchronization

Synchronize pce-memory knowledge across team members. Provides Git hooks integration and CRDT (G-Set) based merge.

## Argument Parsing

Parse `$ARGUMENTS`:
- `push` → Export local knowledge
- `pull` → Import team knowledge
- `status` → Check sync state
- No arguments → Run status and guide

## Operations

### Push (Export)

Export local DB knowledge to `.pce-shared/` directory.

```
pce_memory_sync_push()
```

- Export target: `$PCE_SYNC_TARGET_DIR` (default: `.pce-shared/`)
- If `PCE_SYNC_AUTO_STAGE=true`, auto `git add`
- Scope filter: Restrict with `PCE_SYNC_SCOPE_FILTER`

### Pull (Import)

Import team knowledge from `.pce-shared/`.

```
pce_memory_sync_pull()
// Or dry-run to preview
pce_memory_sync_pull({ dry_run: true })
```

- CRDT (G-Set) based merge: additions only, no deletions
- Boundary promotion: `public < internal < pii < secret` (upgrade only)
- Conflicts: boundary_upgrade auto-resolved, entity/relation diffs skipped

### Status

```
pce_memory_sync_status()
```

Returns:
- Local and remote claim counts
- Unsynced claim count
- Last sync timestamp
- Conflict presence

## Git Hooks Integration

### Setup

```bash
# Install hooks
./scripts/git-hooks/install-hooks.sh

# Set environment
export PCE_SYNC_ENABLED=true
```

### Flow

```
git commit → pre-commit hook → sync push (auto export)
git pull   → post-merge hook → sync pull (auto import)
```

## CRDT Merge Strategy

See [crdt-merge-guide.md](references/crdt-merge-guide.md).

## Troubleshooting

- **sync push fails**: Check state with `pce_memory_state`. Must be Ready to push
- **pull conflicts**: boundary_upgrade auto-resolved. Entity/relation diffs need manual review
- **many unsynced**: Check with `sync status`, then `sync push` → `git commit` → `git push`

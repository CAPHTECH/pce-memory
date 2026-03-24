---
name: pce-sync
context: fork
description: "Team knowledge synchronization skill for pce-memory v2. Manages push/pull/status with memory_type-aware export/import and layer-aware sync rules. Triggered by: 'sync knowledge', 'push knowledge', 'pull team knowledge', 'check sync status'."
argument-hint: '[push|pull|status]'
allowed-tools: 'mcp__pce-memory__pce_memory_sync_push, mcp__pce-memory__pce_memory_sync_pull, mcp__pce-memory__pce_memory_sync_status, mcp__pce-memory__pce_memory_state'
---

# PCE Sync - V2 Team Knowledge Synchronization

Synchronize durable pce-memory knowledge across team members. v2 sync preserves `memory_type` and follows layer-aware export/import rules.

## Argument Parsing

Parse `$ARGUMENTS`:

- `push` → Export local knowledge
- `pull` → Import team knowledge
- `status` → Check sync state
- No arguments → Run status and guide

## Operations

### Push (Export)

Export syncable durable knowledge to `.pce-shared/`.

```
pce_memory_sync_push()
```

- Export target: `$PCE_SYNC_TARGET_DIR` (default: `.pce-shared/`)
- If `PCE_SYNC_AUTO_STAGE=true`, auto `git add`
- Scope filter: Restrict with `PCE_SYNC_SCOPE_FILTER`
- `memory_type` is exported with each durable claim
- Session/micro content is excluded
- Rolled-back or tombstoned durable claims are excluded
- `promotion_queue` is local review state and is never exported

### Pull (Import)

Import team knowledge from `.pce-shared/`.

```
pce_memory_sync_pull()
// Or dry-run to preview
pce_memory_sync_pull({ dry_run: true })
```

- CRDT (G-Set) based merge: additions only, no deletions
- Boundary promotion: `public < internal < pii < secret` (upgrade only)
- `memory_type` is preserved on import and backfilled onto existing claims only when the receiver is missing it
- Session/micro artifacts remain local-only and are not reconstructed from sync
- `promotion_queue` stays local-only because it represents review/rollback governance state
- Conflicts: boundary upgrades auto-resolve, entity/relation diffs are still skipped for manual review

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

## Layer-Aware Rules

- **micro / session**: never sync by default
- **meso / project**: default sync surface
- **macro / principle**: sync only after reviewed durable promotion
- **promotion_queue**: local-only review queue, excluded from Git sync

## CRDT Merge Strategy

See [crdt-merge-guide.md](references/crdt-merge-guide.md).

## Troubleshooting

- **sync push fails**: Check state with `pce_memory_state`. Durable claims must exist before export
- **missing session notes after pull**: Expected. Session/micro observations do not sync
- **rolled-back claim missing from export**: Expected. Rolled-back durable memory is excluded
- **memory_type differs across peers**: Pull backfills missing `memory_type`, but does not overwrite an existing receiver value unless other merge rules apply
- **many unsynced**: Check with `sync status`, then `sync push` -> `git commit` -> `git push`

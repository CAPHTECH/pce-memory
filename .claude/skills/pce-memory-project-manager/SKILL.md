---
name: pce-memory-project-manager
description: Manage CAPHTECH/pce-memory GitHub issue, milestone, and Project #18 workflow using the repo-owned config and scripts. Use when asked to organize milestones, assign issues, maintain the kanban or roadmap, or verify project drift.
---

# pce-memory Project Manager

Manage `CAPHTECH/pce-memory` issue planning through repo-owned automation.

## Use This Skill For

- creating or updating milestones for Project #18
- assigning issues to the configured milestone waves
- syncing Project #18 fields from repo config
- verifying drift between GitHub and repo policy
- checking which operational project views are available

## Source Of Truth

- Config: `docs/project-management/project-18-config.yaml`
- Policy: `docs/project-management/project-18-policy.md`
- Apply script: `scripts/project/apply_project_18.sh`
- Verify script: `scripts/project/verify_project_18.sh`

Read the policy first if the request changes milestone grouping or field conventions.

## Workflow

1. Inspect the current state with:
   `scripts/project/verify_project_18.sh`
2. If the request changes the intended state, update:
   `docs/project-management/project-18-config.yaml`
3. Apply the configured GitHub state with:
   `scripts/project/apply_project_18.sh`
4. Re-run verification.
5. If views are missing or drifted, use the policy doc to reconcile against the existing GitHub default views and then verify again.

## Important Rules

- Treat the repo config as the canonical plan, not the current GitHub state.
- Do not hand-edit individual issue fields first and backfill config later.
- Use the apply script for milestone and field updates to keep history reproducible.
- Keep deferred items in deferred milestones unless the config changes.

## View Boundary

GitHub public APIs do not currently offer a complete Project V2 view-management surface.
This skill therefore treats the existing GitHub views as canonical and verifies these operational views:

- `Team items`
- `Backlog`
- `Roadmap`

## Install

Use `scripts/project/install_skill.sh` to symlink this repo-owned skill into `~/.codex/skills`.

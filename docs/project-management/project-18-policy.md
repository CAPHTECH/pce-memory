# Project #18 Management Policy

This document defines the source of truth for `CAPHTECH/pce-memory` issue management.

## Source Of Truth

- Issues are the work units.
- Milestones define delivery waves.
- GitHub Project #18 is the operational view.
- [`project-18-config.yaml`](./project-18-config.yaml) is the machine-readable source of truth.

## Milestone Policy

- `Wave 1 - Validation Foundation`
  Covers the setup needed to run architecture validation locally.
- `Wave 2 - Memory Architecture Validation`
  Covers validation work for layers, memory types, write path, and retrieval.
- `Wave 3 - v2 Architecture Decision`
  Covers the epic and final v2 architecture decision work.
- `Deferred - Non-v2 Backlog`
  Holds unrelated backlog items.
- `Deferred - v1 Pending v2 Decision`
  Holds v1 issues that should not advance until the v2 direction is settled.

## Project Field Policy

- `Status`
  Use `Backlog`, `Ready`, `In progress`, `In review`, `Done`.
- `Priority`
  Use `P0` for critical path items, `P1` for active follow-up validation work, `P2` for deferred work.
- `Size`
  Use only for active wave issues. Deferred issues stay unset.
- `Start date` and `Target date`
  Use only for active wave issues and roadmap visualization.

## View Policy

GitHub Project public APIs expose view inspection, but not reliable create/rename/filter mutation for Project V2 views.
Because of that, this repository treats the existing GitHub-provided views as the operational source of truth.

- `Team items`
  Canonical table view for the full issue list.
- `Backlog`
  Operational kanban board. It groups vertically by `Status` and sorts by `Priority`.
- `Roadmap`
  Timeline view driven by `Start date` and `Target date`.

If a future authenticated UI session renames or customizes these views, update the config and verification rules first.

## Operational Rules

- Apply changes via [`scripts/project/apply_project_18.sh`](../../scripts/project/apply_project_18.sh).
- Verify drift via [`scripts/project/verify_project_18.sh`](../../scripts/project/verify_project_18.sh).
- If project fields or field option names change in GitHub, update the config and rerun verification.
- Keep the existing `Team items`, `Backlog`, and `Roadmap` views intact unless the config is updated to a new convention.
- Do not create ad hoc milestones or alternative board conventions without updating the config first.

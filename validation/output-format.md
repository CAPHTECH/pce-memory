# Validation Output Artifact Format

This document defines the reference artifact layout for local validation runs and rubric scoring.

It builds on the runtime layout introduced for local validation in Issue #50. The current runner already writes the required run artifacts. Scoring artifacts are additive and may be created by a separate scorer.

## Directory Layout

Store each run under:

```text
validation/local/<YYYY-MM-DD>/<run-id>/
```

Recommended contents:

```text
validation/local/<YYYY-MM-DD>/<run-id>/
├── meta.json
├── prompt.md
├── run.log
├── scorecard.json
├── scorecard.md
└── summary.md
```

## Required Runtime Artifacts

These files should exist for every run:

- `prompt.md`: the exact prompt task file plus any appended input bundle used for the run
- `summary.md`: the model output, following the task's required section structure
- `meta.json`: run metadata and file references
- `run.log`: stdout/stderr trace from the runner

## Optional Scoring Artifacts

These files are recommended once a run is scored:

- `scorecard.json`: machine-readable rubric result
- `scorecard.md`: reviewer-facing summary of scores, failure flags, and notes

The scoring artifacts should never overwrite the original prompt or summary.

## `meta.json` Reference

`meta.json` is the run-metadata contract written by the local validation runner. The schema below matches the current runtime output and reserves optional top-level fields for scored runs.

### JSON Schema

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "title": "LocalValidationMeta",
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "agent": {
      "type": "string",
      "enum": ["codex", "claude"]
    },
    "model": {
      "type": "string",
      "minLength": 1
    },
    "ollama_version": {
      "type": "string",
      "minLength": 1
    },
    "task_id": {
      "type": "string",
      "pattern": "^[A-Za-z0-9._-]+$"
    },
    "run_id": {
      "type": "string",
      "pattern": "^[A-Za-z0-9._-]+$"
    },
    "run_date": {
      "type": "string",
      "format": "date"
    },
    "started_at": {
      "type": "string",
      "format": "date-time"
    },
    "runtime_seconds": {
      "type": "integer",
      "minimum": 0
    },
    "success": {
      "type": "boolean"
    },
    "status": {
      "type": "string",
      "enum": ["prepared", "success", "failure"]
    },
    "summary_path": {
      "type": "string",
      "minLength": 1
    },
    "prompt_path": {
      "type": "string",
      "minLength": 1
    },
    "log_path": {
      "type": "string",
      "minLength": 1
    },
    "notes": {
      "type": "string"
    },
    "input_id": {
      "type": "string",
      "minLength": 1
    },
    "rubric_version": {
      "type": "string",
      "minLength": 1
    },
    "scorecard_path": {
      "type": "string",
      "minLength": 1
    }
  },
  "required": [
    "agent",
    "model",
    "ollama_version",
    "task_id",
    "run_id",
    "run_date",
    "started_at",
    "runtime_seconds",
    "success",
    "status",
    "summary_path",
    "prompt_path",
    "log_path",
    "notes"
  ]
}
```

### Behavioral invariants

- `status=prepared` should be paired with `success=false` and `runtime_seconds=0`.
- `status=success` should be paired with `success=true`.
- `summary_path`, `prompt_path`, and `log_path` are relative to the run directory.
- `input_id`, `rubric_version`, and `scorecard_path` are optional scoring-era fields and should be absent until a run is scored.

### Example instance

```json
{
  "agent": "codex",
  "model": "qwen3.5:122b-a10b",
  "ollama_version": "0.17.7",
  "task_id": "resume_task",
  "run_id": "codex-123456-999",
  "run_date": "2026-03-24",
  "started_at": "2026-03-24T01:00:00Z",
  "runtime_seconds": 42,
  "success": true,
  "status": "success",
  "summary_path": "summary.md",
  "prompt_path": "prompt.md",
  "log_path": "run.log",
  "notes": "Canonical scored run.",
  "input_id": "resume_task.example.001",
  "rubric_version": "validation/rubric.md@2026-03-24",
  "scorecard_path": "scorecard.json"
}
```

## `prompt.md` Reference

`prompt.md` should preserve the exact evaluation input:

1. The canonical task prompt from `validation/tasks/<task-id>.md`
2. The appended task-specific input bundle, if any
3. No post-hoc edits after execution

This file is the reproducibility anchor for the run.

## `summary.md` Reference

`summary.md` should contain the raw agent answer only.

Requirements:

- follow the exact section structure defined by the selected task file
- keep evidence references inline with the answer
- avoid including scorer commentary or later annotations

## `scorecard.json` Reference

Use this structure when storing rubric results:

The `dimension_scores` keys must match the canonical keys listed in `validation/rubric.md`.

```json
{
  "task_id": "resume_task",
  "run_id": "codex-123456-999",
  "rubric_version": "validation/rubric.md@2026-03-24",
  "scored_at": "2026-03-24T01:00:00Z",
  "verdict": "strong_pass|pass|weak|fail",
  "total_score": 16,
  "normalized_score": 80,
  "dimension_scores": {
    "usefulness_actionability": { "score": 3, "notes": "string" },
    "provenance_sufficiency": { "score": 4, "notes": "string" },
    "contamination_risk": { "score": 3, "notes": "string" },
    "policy_invariant_correctness": { "score": 3, "notes": "string" },
    "retrieval_relevance": { "score": 3, "notes": "string" }
  },
  "failure_flags": ["retrieval_noise"],
  "hard_fail": false,
  "reviewer": "string"
}
```

## `scorecard.md` Reference

`scorecard.md` is optional, but recommended for human review. Keep it short and stable:

```markdown
# Scorecard

- task_id: `resume_task`
- run_id: `codex-123456-999`
- verdict: `pass`
- total_score: `16/20`
- normalized_score: `80`
- failure_flags: `retrieval_noise`

## Dimension Notes

- usefulness_actionability: ...
- provenance_sufficiency: ...
- contamination_risk: ...
- policy_invariant_correctness: ...
- retrieval_relevance: ...
```

## Compatibility Note

The current helper scripts already produce `meta.json`, `prompt.md`, `run.log`, and `summary.md`.

`scorecard.json` and `scorecard.md` are forward-compatible additions for corpus scoring. A run remains valid without them until automated scoring is added.

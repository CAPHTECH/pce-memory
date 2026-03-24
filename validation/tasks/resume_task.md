# Local Validation Task: Resume Task

You are validating whether pce-memory can help an agent resume an interrupted task without re-reading the entire repository.

## Goal

Confirm that a local agent can reconstruct task state from a compact retrieved context, separate confirmed facts from uncertainty, and propose a short restart plan.

This is not a benchmark and not a model comparison task.

## Required Repository Inputs

Inspect at least these files before answering:

- `README.md`
- `docs/pce-memory-vision.md`
- `docs/mcp-tools.md`
- `docs/pce-memory-usefulness-review.ja.md`

You may inspect additional files if needed.

## Canonical Prompt / Input Shape

Append one input bundle to this task using JSON with at least these fields:

```json
{
  "task_request": "string",
  "current_goal": "string",
  "time_gap": "PT8H",
  "known_progress": ["string"],
  "constraints": ["string"],
  "open_questions": ["string"],
  "active_context": [
    {
      "claim_id": "clm_...",
      "scope": "session|project|principle",
      "boundary_class": "public|internal|pii|secret",
      "kind": "ClaimKind",
      "text": "string",
      "score": 0.0,
      "provenance": [
        {
          "at": "2026-03-24T00:00:00Z",
          "actor": "string",
          "git": {
            "commit": "abcdef1",
            "repo": "CAPHTECH/pce-memory",
            "files": ["path/to/file"]
          },
          "note": "string"
        }
      ]
    }
  ]
}
```

The input bundle should be small enough for repeated local runs. Treat `active_context` as retrieved memory, not as unquestioned truth.

## Questions to Answer

1. What task state can be recovered with high confidence?
2. Which claims are stale, ambiguous, or missing and need refresh?
3. What are the next 3 concrete steps to resume work safely?
4. Which memory items should be kept, downgraded, or discarded before continuing?

## Output Format

Return exactly these sections:

```markdown
# Recovered Task State

# Confidence And Gaps

# Resume Plan

# Memory Hygiene

# Evidence
```

In `# Evidence`, cite repository files and any input-bundle `claim_id` values that materially support the answer.

These sections are chosen to expose the rubric dimensions. Use the exact canonical keys from `validation/rubric.md` when scoring:

- `usefulness_actionability`: `# Resume Plan`
- `provenance_sufficiency`: `# Evidence`
- `contamination_risk`: `# Confidence And Gaps` and `# Memory Hygiene`
- `policy_invariant_correctness`: `# Memory Hygiene` should state whether any `scope`, `boundary_class`, freshness, or promotion rule blocks direct reuse or distillation.
- `retrieval_relevance`: `# Recovered Task State` and `# Evidence`

If a dimension has no material issue, say that explicitly in the mapped section instead of leaving it implicit.

## Evaluation Criteria

- Reconstructs the current goal and progress from the input bundle plus repository evidence.
- Separates confirmed facts, reasonable inferences, and unresolved gaps instead of blending them together.
- Produces an immediately actionable resume plan with ordering, dependencies, and safety checks.
- Identifies low-confidence or stale memory that should be refreshed, downgraded, or excluded.
- Makes any `scope`, `boundary_class`, or freshness constraint explicit before recommending reuse or promotion.
- Uses provenance in a way that lets a reviewer trace where key conclusions came from.
- Primary rubric emphasis: `usefulness_actionability`, `retrieval_relevance`, `provenance_sufficiency`.

## Failure Patterns

- `expired_ac_assumption`: treats retrieved `active_context` or stale task notes as current without calling for refresh.
- `scope_promotion_error`: treats `session` task state or tentative notes as durable `project` or `principle` memory.
- `activate_skip_resume`: falls back to generic restart advice or full rereads instead of using retrieved context plus targeted refresh.
- `memory_hygiene_omission`: repeats retrieved claims without keep, refresh, or drop judgment.
- `provenance_drop`: omits file paths or `claim_id` references for key resume decisions.

## Constraints

- Prefer repository and input-bundle evidence over generic advice.
- Keep the answer concise enough for repeated local execution.
- If the input bundle is insufficient, say so explicitly instead of guessing.
- Score resulting artifacts with `validation/rubric.md`.

# Local Validation Task: Design Decision

You are validating whether pce-memory can help an agent make or revisit a design decision using retrieved context, explicit constraints, and repository-grounded tradeoffs.

## Goal

Confirm that a local agent can surface existing commitments, compare options, make a bounded recommendation, and draft a decision record that could be stored with provenance.

This is not a benchmark and not a model comparison task.

## Required Repository Inputs

Inspect at least these files before answering:

- `README.md`
- `docs/pce-memory-vision.md`
- `docs/boundary-policy.md`
- `docs/activation-ranking.md`
- `docs/mcp-tools.md`

You may inspect additional files if needed.

## Canonical Prompt / Input Shape

Append one input bundle to this task using JSON with at least these fields:

```json
{
  "decision_question": "string",
  "decision_deadline": "string",
  "options": [
    {
      "id": "option_a",
      "description": "string"
    }
  ],
  "constraints": ["string"],
  "non_goals": ["string"],
  "active_context": [
    {
      "claim_id": "clm_...",
      "scope": "session|project|principle",
      "boundary_class": "public|internal|pii|secret",
      "kind": "fact|preference|task|policy_hint",
      "text": "string",
      "score": 0.0,
      "provenance": [{ "at": "2026-03-24T00:00:00Z" }]
    }
  ]
}
```

The `active_context` should capture prior decisions, invariants, or known constraints that might affect the choice.

## Questions to Answer

1. Which existing commitments and invariants are relevant to this decision?
2. What are the main tradeoffs for each option?
3. Which option should be recommended now, and why?
4. What short decision record should be written back to memory if the recommendation is adopted?

## Output Format

Return exactly these sections:

```markdown
# Decision Context

# Existing Commitments

# Option Analysis

# Recommendation

# Decision Record Draft

# Evidence
```

In `# Decision Record Draft`, provide a compact, provenance-ready draft that could be turned into an upsert payload.

These sections are chosen to expose the rubric dimensions. Use the exact canonical keys from `validation/rubric.md` when scoring:

- `usefulness_actionability`: `# Recommendation` and `# Decision Record Draft`
- `provenance_sufficiency`: `# Evidence`
- `contamination_risk`: `# Option Analysis` should separate durable constraints from low-confidence session preferences or stale context.
- `policy_invariant_correctness`: `# Existing Commitments` and `# Recommendation` should make boundary, invariant, and scope constraints explicit.
- `retrieval_relevance`: `# Decision Context`, `# Existing Commitments`, and `# Evidence`

If a dimension has no material issue, say that explicitly in the mapped section instead of leaving it implicit.

## Evaluation Criteria

- Uses retrieved memory and repository docs to frame the decision instead of defaulting to generic best practices.
- Distinguishes durable constraints from temporary session context.
- Compares at least the provided options with concrete tradeoffs, not slogans.
- Makes a recommendation that is bounded, actionable, and consistent with existing invariants.
- Produces a draft decision record that is concise enough to store and trace later.
- Primary rubric emphasis: `provenance_sufficiency`, `usefulness_actionability`, `retrieval_relevance`.

## Failure Patterns

- `context_free_optioning`: recommends an option without using retrieved commitments or repository constraints.
- `retrieval_override_by_preference`: lets low-confidence or `session`-scoped context override `project` or `principle` commitments.
- `policy_unaware_tradeoff`: compares options without accounting for existing boundary or invariant constraints.
- `non_upsertable_decision_record`: gives a recommendation but no concise record that could be upserted with provenance.
- `evidence_thin_tradeoff`: names tradeoffs but cannot trace them back to files or retrieved claims.

## Constraints

- Stay grounded in repository evidence and the supplied input bundle.
- Make uncertainty explicit where retrieved context conflicts or is incomplete.
- Keep the decision record short enough for repeated evaluation runs.
- Score resulting artifacts with `validation/rubric.md`.

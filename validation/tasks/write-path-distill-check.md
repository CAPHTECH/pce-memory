# Local Validation Task: Write Path Distill Check

You are validating whether the current repository has enough structure to support an explicit observe -> distill -> promote write path.

## Required Repository Inputs

Inspect at least these files before answering:

- `README.md`
- `docs/pce-memory-vision.md`
- `docs/boundary-policy.md`
- `docs/mcp-tools.md`

## Questions to Answer

1. Which parts of the current codebase or docs already imply an observe -> distill -> promote pipeline?
2. Which invariants are missing or only implicit?
3. Where would the main failure modes appear first?
4. Which implementation gaps should be addressed before introducing automated promotion?

## Output Format

Return exactly these sections:

```markdown
# Existing Signals

# Missing Invariants

# Failure Modes

# Recommended Next Checks

# Evidence
```

## Constraints

- Stay within repository evidence.
- Do not compare vendors or models.
- Focus on invariants, not product positioning.

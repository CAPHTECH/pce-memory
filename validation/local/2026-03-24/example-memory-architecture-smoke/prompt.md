# Local Validation Task: Memory Architecture Smoke

You are validating the current pce-memory architecture from the repository contents only.

## Goal

Confirm that a local agent can inspect the repository, reason about the design, and return a structured architecture note.

This is not a benchmark and not a model comparison task.

## Required Repository Inputs

Inspect at least these files before answering:

- `README.md`
- `docs/pce-memory-vision.md`
- `docs/boundary-policy.md`
- `docs/core-types.md`

You may inspect additional files if needed.

## Questions to Answer

1. What are the current memory layers in the repository, and how do `session`, `project`, and `principle` map onto the design?
2. What are the main promotion risks around the observe -> distill -> promote path?
3. What are the main retrieval risks in the current architecture?
4. Which validation checks should be run next to reduce architectural uncertainty?

## Output Format

Return exactly these sections:

```markdown
# Memory Layers

# Promotion Risks

# Retrieval Risks

# Validation Checks

# Evidence
```

## Constraints

- Prefer repository evidence over general background knowledge.
- Cite file paths in `# Evidence`.
- Keep the answer concise and architecture-focused.

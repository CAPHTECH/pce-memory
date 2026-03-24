# Local Validation Artifacts

Runtime artifacts created by `scripts/local/run-validation-smoke.sh` are written under:

```text
validation/local/<YYYY-MM-DD>/<run-id>/
```

Each run directory contains:

- `summary.md` - agent answer
- `meta.json` - run metadata
- `prompt.md` - exact task prompt
- `run.log` - stdout/stderr trace

This directory keeps one checked-in sample artifact:

- `validation/local/2026-03-24/example-memory-architecture-smoke/`

Additional local runs are ignored by default unless you explicitly add them to Git.

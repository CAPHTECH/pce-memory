# Memory Layers

- `session` is the fast layer used for short-lived working context and maps cleanly to the micro layer described in the policy and core type docs.
- `project` is the medium layer for repeatable team or repository knowledge and maps to the meso layer.
- `principle` is the slow layer for durable rules and maps to the macro layer.

# Promotion Risks

- The repository documents distillation and promotion, but the path is still more explicit in docs than in a first-class promoted workflow, so local validation should check where promotion remains implicit.
- Promotion can overfit transient session findings if provenance and review requirements are not enforced at the handoff from active context to longer-lived claims.
- Boundary checks must remain monotonic during promotion so that micro discoveries do not bypass macro safety constraints.

# Retrieval Risks

- Retrieval behavior is policy-driven and hybrid, so local validation should check whether text-heavy results dominate when vector evidence is weak or unavailable.
- Layer-aware retrieval can regress if `session`, `project`, and `principle` are retrieved as a flat set instead of a paced hierarchy.
- Long prompts against a local model can hide evidence quality problems because the model may summarize confidently even when the recall set is partial.

# Validation Checks

1. Verify that smoke-task answers consistently identify the same layer mapping from `README.md`, `docs/boundary-policy.md`, and `docs/core-types.md`.
2. Check whether architecture prompts can surface explicit promotion invariants from `docs/pce-memory-vision.md` without drifting into generic advice.
3. Run the deeper `write-path-distill-check` task and compare whether the agent identifies the same missing invariants across repeated runs.
4. Capture latency, success/failure, and evidence quality in `meta.json` so local reliability problems remain visible.

# Evidence

- `README.md`
- `docs/pce-memory-vision.md`
- `docs/boundary-policy.md`
- `docs/core-types.md`

# Scope, Layer, and Boundary Guide

## Scope Selection

### session -> micro (fast-changing, local-only)

- **When**: Information valid only for the current session or branch moment
- **Examples**: "Editing this file", "Debugging hypothesis", "Temporary state"
- **Write path**: Use `observe`, not `upsert`
- **Sync posture**: Never sync by default

### project -> meso (durable project knowledge)

- **When**: Project-specific decisions and patterns
- **Examples**: "JWT for auth", "Vitest for testing", "REST API design", "DuckDB storage"
- **Write path**: `distill -> promote` or the narrow `upsert` escape hatch
- **Sync posture**: Default sync surface

### principle -> macro (reviewed norms and policies)

- **When**: Universal principles applicable across projects
- **Examples**: "TDD development", "SOLID principles", "fp-ts/Either for errors"
- **Write path**: Reviewed `distill -> promote`, or reviewed `upsert`
- **Sync posture**: Explicit, reviewed sync only

## Memory Type Selection

### evidence

- **When**: Raw logs, outputs, and source material
- **Durability**: Micro only, not a canonical durable claim target

### working_state

- **When**: Reusable active task state that should survive sessions after review

### knowledge

- **When**: Stable facts, architecture decisions, resolved root causes

### procedure

- **When**: Repeatable workflows, migration steps, operational runbooks

### norm

- **When**: Reviewed principles, policies, invariants, and constraints

## Boundary Class Selection

### public

- **When**: Publicly shareable information
- **Examples**: OSS library usage, general technical patterns, public API specs

### internal

- **When**: Internal/project-only information
- **Examples**: Internal API specs, architecture decisions, internal tool configs

### pii

- **When**: Context containing personal information
- **Examples**: Design decisions involving usernames, email addresses
- **Note**: Anonymize before durable promotion when possible

### secret

- **When**: Sensitive information that must remain non-durable
- **Examples**: API keys, auth tokens, passwords
- **Note**: Use `observe` only when absolutely necessary. `upsert(secret)` is rejected.

## Decision Flowchart

```
Is this raw session evidence or temporary work state?
├─ Yes → observe into micro
└─ No → Is it already distilled durable knowledge?
         ├─ No → distill first
         └─ Yes → promote or use the upsert escape hatch
```

## Common Combinations

| Scope / layer       | Boundary   | Example                                        |
| ------------------- | ---------- | ---------------------------------------------- |
| session / micro     | internal   | Internal API behavior notes during debugging   |
| session / micro     | secret     | Temporary secret-bearing logs kept local only  |
| project / meso      | internal   | Project-specific DB design decisions           |
| project / meso      | public     | OSS library selection rationale                |
| principle / macro   | public     | TDD adoption policy                            |
| principle / macro   | internal   | Internal coding standards                      |

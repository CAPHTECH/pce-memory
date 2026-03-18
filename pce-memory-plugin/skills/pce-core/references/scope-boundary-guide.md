# Scope & Boundary Class Guide

## Scope Selection

### session (fast-changing)

- **When**: Information valid only for the current session
- **Examples**: "Editing this file", "Debugging hypothesis", "Temporary state"
- **Lifespan**: Until session ends

### project (medium-changing)

- **When**: Project-specific decisions and patterns
- **Examples**: "JWT for auth", "Vitest for testing", "REST API design", "DuckDB storage"
- **Lifespan**: Duration of the project

### principle (slow-changing)

- **When**: Universal principles applicable across projects
- **Examples**: "TDD development", "SOLID principles", "fp-ts/Either for errors"
- **Lifespan**: Long-term (rarely changes)

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
- **Note**: Anonymize before recording when possible

### secret

- **When**: Sensitive information (**strongly recommend NOT recording**)
- **Examples**: API keys, auth tokens, passwords
- **Note**: Record only references, never actual secrets

## Decision Flowchart

```
Is the information publicly shareable?
├─ Yes → public
└─ No → Contains personal information?
         ├─ Yes → pii (consider anonymizing)
         └─ No → Sensitive/secret?
                  ├─ Yes → secret (do not record)
                  └─ No → internal
```

## Scope × Boundary Combinations

| Scope                | Boundary                                     | Example |
| -------------------- | -------------------------------------------- | ------- |
| session + internal   | Internal API behavior notes during debugging |
| project + internal   | Project-specific DB design decisions         |
| project + public     | OSS library selection rationale              |
| principle + public   | TDD adoption policy                          |
| principle + internal | Internal coding standards                    |

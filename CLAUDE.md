# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build & Development Commands

```bash
# Install dependencies (monorepo)
pnpm install

# Build all packages
pnpm build

# Run all tests
pnpm test

# Run single test file
pnpm test apps/pce-memory/test/specific.test.ts

# Property-based tests only
pnpm test:pbt

# Type checking
pnpm typecheck

# Linting
pnpm lint
pnpm lint:fix

# Formatting
pnpm format
pnpm format:check

# Formal verification (TLA+/Alloy)
pnpm formal:tla
pnpm formal:alloy
```

### pce-memory (MCP Server) specific

```bash
cd apps/pce-memory

# Development mode
pnpm dev

# Build
pnpm build

# Run tests
pnpm test

# Type check
pnpm typecheck
```

## Architecture Overview

### Monorepo Structure

- `apps/pce-memory` - MCP server (main package, published to npm as `pce-memory`)
- `packages/pce-boundary` - Boundary validation & redaction
- `packages/pce-embeddings` - Embedding provider abstraction (OpenAI/Local)
- `packages/pce-policy-schemas` - YAML policy schemas
- `packages/pce-sdk-ts` - TypeScript client SDK

### pce-memory Internal Architecture

```
src/
├── index.ts          # MCP server entry (stdio transport)
├── core/handlers.ts  # Tool handlers (central dispatcher)
├── domain/           # State machine, errors, validation
├── store/            # DuckDB persistence (claims, entities, relations, etc.)
├── state/            # Runtime state (memoryState, layerScopeState)
├── daemon/           # Standalone daemon process
└── client/           # Proxy client (auto-starts daemon)
```

### State Machine Flow

```
Uninitialized → PolicyApplied → HasClaims → Ready
                     │              │          │
                     └──────────────┴──────────┘ (循環可能)
```

- `policy_apply` - Initialize with policy (Uninitialized → PolicyApplied)
- `upsert` - Register claims (PolicyApplied/HasClaims/Ready → HasClaims)
- `activate` - Build active context (HasClaims/Ready → Ready)
- `feedback` - Update critic scores (Ready state only)

### MCP Tools

| Tool                           | Description                                        |
| ------------------------------ | -------------------------------------------------- |
| `pce.memory.policy.apply`      | Apply policy (initialization)                      |
| `pce.memory.upsert`            | Register claim with entities/relations             |
| `pce.memory.upsert.entity`     | Register graph entity                              |
| `pce.memory.upsert.relation`   | Register graph relation                            |
| `pce.memory.activate`          | Build active context (hybrid search)               |
| `pce.memory.feedback`          | Update critic (helpful/harmful/outdated/duplicate) |
| `pce.memory.boundary.validate` | Pre-generation boundary check                      |
| `pce.memory.state`             | Get current state                                  |

## Testing Approach

This project uses **Law-Driven Engineering (LDE)**:

1. **fp-ts/Either** for error handling (no exceptions)
2. **Property-based testing** with fast-check (prefix: `Property:`)
3. **Detroit School TDD** - test actual component integration
4. **exactOptionalPropertyTypes: true** - strict optional property handling

### Test Conventions

```typescript
// Use spread syntax for optional properties
const entity = await upsertEntity({
  id,
  type,
  name,
  ...(optional !== undefined && { optional }),
});
```

## Key Concepts

### Pace Layering (Scope)

| Scope       | Change Rate | Use Case                        |
| ----------- | ----------- | ------------------------------- |
| `session`   | Fast        | Session-specific temporary info |
| `project`   | Medium      | Project-specific patterns       |
| `principle` | Slow        | Universal principles            |

### Boundary Classes

| Class      | Use Case                    |
| ---------- | --------------------------- |
| `public`   | Publicly shareable          |
| `internal` | Internal only               |
| `pii`      | Contains personal info      |
| `secret`   | Credentials (avoid storing) |

## Environment Variables

| Variable          | Description                         | Default    |
| ----------------- | ----------------------------------- | ---------- |
| `PCE_DB`          | DuckDB file path                    | `:memory:` |
| `PCE_RATE_CAP`    | Rate limit per bucket               | `1000`     |
| `PCE_RATE_WINDOW` | Rate window (seconds)               | `10`       |
| `PCE_TOKEN`       | Auth token (required in production) | -          |

## Quality Gates

| Gate                  | Threshold |
| --------------------- | --------- |
| Static Analysis       | 0 errors  |
| Coverage              | ≥ 80%     |
| Cyclomatic Complexity | ≤ 10      |

---

@AGENTS.md

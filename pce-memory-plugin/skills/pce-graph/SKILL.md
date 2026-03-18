---
name: pce-graph
context: fork
description: "Knowledge graph operations skill for pce-memory. Create, query, and visualize entities and relations. Triggered by: 'create entity', 'graph relation', 'query knowledge graph', 'map dependencies'."
argument-hint: '[entity|relation|query] [args...]'
allowed-tools: 'mcp__pce-memory__pce_memory_upsert_entity, mcp__pce-memory__pce_memory_upsert_relation, mcp__pce-memory__pce_memory_query_entity, mcp__pce-memory__pce_memory_query_relation, mcp__pce-memory__pce_memory_state'
---

# PCE Graph - Knowledge Graph Operations

Operate on the pce-memory knowledge graph (entities and relations).

## Argument Parsing

Parse `$ARGUMENTS`:

- `entity [name] [type]` → Create/search entity
- `relation [from] [to] [type]` → Create relation
- `query [pattern]` → Search graph
- No arguments → Interactive guide

## Entity Operations

### Creating Entities

Register important codebase components as entities.

```
pce_memory_upsert_entity({
  id: "entity-unique-id",
  type: "component|module|api|database|service|concept",
  name: "Display name",
  properties: { ... }  // Optional additional info
})
```

### Entity Type Guide

See [entity-relation-patterns.md](references/entity-relation-patterns.md).

| Type      | Purpose            | Examples                     |
| --------- | ------------------ | ---------------------------- |
| component | Software component | AuthService, UserController  |
| module    | Module/package     | pce-boundary, pce-embeddings |
| api       | API endpoint       | POST /api/claims             |
| database  | Data store         | DuckDB, Redis                |
| service   | External service   | OpenAI API, GitHub           |
| concept   | Concept/pattern    | State Machine, CRDT          |

### Querying Entities

```
pce_memory_query_entity({
  type: "component",     // Filter by type
  name_pattern: "Auth*"  // Filter by name pattern
})
```

## Relation Operations

### Creating Relations

Register relationships between entities.

```
pce_memory_upsert_relation({
  from_id: "entity-a",
  to_id: "entity-b",
  relation_type: "depends_on|implements|contains|calls|stores_in",
  properties: { ... }
})
```

### Relation Type Guide

| Type       | Meaning            | Example                            |
| ---------- | ------------------ | ---------------------------------- |
| depends_on | Dependency         | AuthService depends_on JWTLibrary  |
| implements | Implementation     | UserController implements IUserAPI |
| contains   | Containment        | CoreModule contains StateManager   |
| calls      | Invocation         | Handler calls Repository           |
| stores_in  | Persistence target | ClaimStore stores_in DuckDB        |

### Querying Relations

```
pce_memory_query_relation({
  from_id: "entity-a",        // Filter by source
  relation_type: "depends_on" // Filter by type
})
```

## Typical Workflows

### Dependency Mapping

1. Register key components as entities
2. Register inter-component dependencies as relations
3. Visualize dependency tree with `query_relation`

### Architecture Recording

1. Register layers/modules as entities
2. Register contains/implements relations
3. Link design decisions (claims via upsert) to entities

# Entity-Relation Patterns

## Pattern 1: Microservices Architecture

```
[API Gateway] --calls--> [Auth Service] --stores_in--> [Redis]
                          |
                          --depends_on--> [JWT Library]

[API Gateway] --calls--> [User Service] --stores_in--> [PostgreSQL]
```

Entities:

- `api-gateway` (type: service)
- `auth-service` (type: component)
- `user-service` (type: component)
- `redis` (type: database)
- `postgresql` (type: database)
- `jwt-library` (type: module)

## Pattern 2: Monorepo Package Structure

```
[Root] --contains--> [apps/pce-memory] --depends_on--> [packages/pce-boundary]
                                        --depends_on--> [packages/pce-embeddings]
                                        --depends_on--> [packages/pce-sdk-ts]
```

## Pattern 3: State Machine

```
[StateMachine] --contains--> [Uninitialized]
               --contains--> [PolicyApplied]
               --contains--> [HasClaims]
               --contains--> [Ready]

[Uninitialized] --transitions_to--> [PolicyApplied] (via: policy_apply)
[PolicyApplied] --transitions_to--> [HasClaims] (via: upsert)
[HasClaims] --transitions_to--> [Ready] (via: activate)
```

## Pattern 4: API Structure

```
[POST /claims] --implements--> [ClaimHandler]
               --stores_in--> [DuckDB]
[GET /activate] --implements--> [ActivateHandler]
                --calls--> [EmbeddingProvider]
```

## Naming Conventions

- Entity ID: kebab-case (`auth-service`, `user-controller`)
- Display name: PascalCase or natural language (`AuthService`, `Auth Service`)
- Relation type: snake_case (`depends_on`, `stores_in`)

## Properties Examples

```json
// Entity properties
{
  "version": "2.0",
  "language": "TypeScript",
  "test_coverage": "85%",
  "owner": "backend-team"
}

// Relation properties
{
  "strength": "strong",
  "direction": "unidirectional",
  "protocol": "HTTP/REST"
}
```

# Entity-Relation Patterns

## パターン 1: マイクロサービスアーキテクチャ

```
[API Gateway] --calls--> [Auth Service] --stores_in--> [Redis]
                          |
                          --depends_on--> [JWT Library]

[API Gateway] --calls--> [User Service] --stores_in--> [PostgreSQL]
```

エンティティ:
- `api-gateway` (type: service)
- `auth-service` (type: component)
- `user-service` (type: component)
- `redis` (type: database)
- `postgresql` (type: database)
- `jwt-library` (type: module)

## パターン 2: モノレポパッケージ構造

```
[Root] --contains--> [apps/pce-memory] --depends_on--> [packages/pce-boundary]
                                        --depends_on--> [packages/pce-embeddings]
                                        --depends_on--> [packages/pce-sdk-ts]
```

## パターン 3: 状態マシン

```
[StateMachine] --contains--> [Uninitialized]
               --contains--> [PolicyApplied]
               --contains--> [HasClaims]
               --contains--> [Ready]

[Uninitialized] --transitions_to--> [PolicyApplied] (via: policy_apply)
[PolicyApplied] --transitions_to--> [HasClaims] (via: upsert)
[HasClaims] --transitions_to--> [Ready] (via: activate)
```

## パターン 4: API構造

```
[POST /claims] --implements--> [ClaimHandler]
               --stores_in--> [DuckDB]
[GET /activate] --implements--> [ActivateHandler]
                --calls--> [EmbeddingProvider]
```

## 命名規約

- エンティティID: kebab-case (`auth-service`, `user-controller`)
- 表示名: PascalCase or 自然言語 (`AuthService`, `認証サービス`)
- リレーションタイプ: snake_case (`depends_on`, `stores_in`)

## properties の活用例

```json
// エンティティのproperties
{
  "version": "2.0",
  "language": "TypeScript",
  "test_coverage": "85%",
  "owner": "backend-team"
}

// リレーションのproperties
{
  "strength": "strong",
  "direction": "unidirectional",
  "protocol": "HTTP/REST"
}
```

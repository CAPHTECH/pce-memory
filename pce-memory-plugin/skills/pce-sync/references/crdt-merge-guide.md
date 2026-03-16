# CRDT Merge Guide

## G-Set CRDT

pce-memory sync is based on G-Set (Grow-only Set) CRDT.

### Properties

- **Append-only**: Claims can only be added, never deleted
- **Idempotent**: Adding the same claim multiple times yields the same result
- **Commutative**: Order of additions does not affect the result
- **Associative**: (A ∪ B) ∪ C = A ∪ (B ∪ C)

### Deduplication via content_hash

Claims with the same `content_hash` are considered identical and deduplicated during merge.

```
Local:  { hash: "abc", text: "Using JWT for auth" }
Remote: { hash: "abc", text: "Using JWT for auth" }
Result: { hash: "abc", text: "Using JWT for auth" }  ← only one remains
```

## Boundary Monotonicity

Boundary class is monotonically increasing (upgrade only).

```
public < internal < pii < secret
```

### Merge Rules

When the same claim exists with different boundaries, the stricter one is adopted.

```
Local:  { hash: "abc", boundary: "public" }
Remote: { hash: "abc", boundary: "internal" }
Result: { hash: "abc", boundary: "internal" }  ← stricter wins
```

### Auto-resolution

`boundary_upgrade` conflicts are automatically resolved to the higher level. No user intervention needed.

## Conflict Types

| Type | Resolution | Auto/Manual |
|------|-----------|-------------|
| Duplicate claim (same hash) | Merge (consolidate to one) | Auto |
| Boundary upgrade | Adopt stricter level | Auto |
| Entity attribute diff | Skip (local priority) | Manual review recommended |
| Relation diff | Skip (local priority) | Manual review recommended |

## Best Practices

1. **Push frequently**: Avoid large unsynced backlogs
2. **Check status before pull**: Preview conflicts beforehand
3. **Be careful with boundaries**: Once upgraded, cannot be downgraded
4. **content_hash is required**: Essential for deduplication

# CRDT Merge Guide

## G-Set CRDT

pce-memoryの同期はG-Set（Grow-only Set）CRDTを基盤とする。

### 特性

- **追加のみ**: Claimは追加されるだけで、削除されない
- **冪等性**: 同じClaimを複数回追加しても結果は同じ
- **可換性**: 追加の順序は結果に影響しない
- **結合性**: (A ∪ B) ∪ C = A ∪ (B ∪ C)

### content_hash による重複排除

同じ `content_hash` を持つClaimは同一とみなされ、マージ時に重複排除される。

```
Local:  { hash: "abc", text: "JWTで認証" }
Remote: { hash: "abc", text: "JWTで認証" }
Result: { hash: "abc", text: "JWTで認証" }  ← 1つだけ残る
```

## Boundary Monotonicity

Boundaryクラスは単調増加（昇格のみ）。

```
public < internal < pii < secret
```

### マージルール

同じClaimが異なるboundaryで存在する場合、より厳しい方が採用される。

```
Local:  { hash: "abc", boundary: "public" }
Remote: { hash: "abc", boundary: "internal" }
Result: { hash: "abc", boundary: "internal" }  ← より厳しい方
```

### 自動解決

`boundary_upgrade` コンフリクトは自動的に上位に解決される。ユーザー介入不要。

## コンフリクトの種類

| 種類 | 解決方法 | 自動/手動 |
|------|----------|-----------|
| 重複Claim（同hash） | マージ（1つに統合） | 自動 |
| Boundary昇格 | より厳しい方を採用 | 自動 |
| Entity属性差分 | スキップ（ローカル優先） | 手動確認推奨 |
| Relation差分 | スキップ（ローカル優先） | 手動確認推奨 |

## ベストプラクティス

1. **こまめにpush**: 大量の未同期を避ける
2. **pull前にstatus確認**: コンフリクトの有無を事前チェック
3. **boundary は慎重に**: 一度昇格すると降格できない
4. **content_hash は必須**: 重複排除の要

# ADR-0002: APIインターフェース設計（状態機械パターン採用）

## ステータス

採択済み（2024-11-25）

## コンテキスト

PCE-MemoryのAPIインターフェース設計について、形式検証（Alloy）を用いて3つの設計パターンを比較評価した。

### 評価した設計パターン

| 設計 | 概要 |
|------|------|
| A: フラットAPI | 全操作がいつでも呼び出し可能 |
| B: ビルダーAPI | 段階的構築、完成まで実行不可 |
| C: 状態機械API | 状態ごとに許可操作を型レベルで制限 |

### 形式検証の結果（Alloy）

```
FlatAPI_UnsafeUpsert            SAT   ← 反例発見（不安全）
Builder_CompleteOnlyAfterAllFields   SAT   ← 反例発見
SM_UpsertRequiresPolicy         UNSAT ← 成立（安全）
SM_ActivateRequiresClaims       UNSAT ← 成立（安全）
```

### 発見された問題

**設計A（フラットAPI）**:
- `policyApplied = False` の状態で `Upsert()` 呼び出しが可能
- 実行時エラーとして処理される（呼び出し自体は防げない）

**設計B（ビルダーAPI）**:
- 順序は強制されるが、`policyApplied = False` でも `Build()` 可能
- 実行時エラーとして処理される

**設計C（状態機械API）**:
- 不正な呼び出しは状態遷移として定義されていない
- コンパイル時に排除される（反例なし）

## 決定

**設計C（状態機械API）を採用する。**

### 理由

1. **型安全性**: 不正な呼び出しがコンパイル時に検出される
2. **エラーパス削減**: 実行時エラーパスが存在しない
3. **形式検証で証明済み**: `SM_UpsertRequiresPolicy`、`SM_ActivateRequiresClaims` が成立

### 採用しない設計

| 設計 | 不採用理由 |
|------|-----------|
| A: フラットAPI | 不正呼び出しが実行時まで検出されない |
| B: ビルダーAPI | ポリシー適用チェックが実行時依存 |

## 設計詳細

### 状態遷移図

```
┌───────────────┐
│ Uninitialized │
└───────┬───────┘
        │ applyPolicy()
        ▼
┌───────────────┐
│ PolicyApplied │
└───────┬───────┘
        │ upsert()
        ▼
┌───────────────┐
│   HasClaims   │◄──┐
└───────┬───────┘   │ upsert() (追加)
        │           │
        └───────────┘
        │ activate()
        ▼
┌───────────────┐
│     Ready     │
└───────────────┘
        │ feedback()
        ▼
      (継続)
```

### 各状態で許可される操作

| 状態 | 許可操作 |
|------|---------|
| Uninitialized | `applyPolicy()` のみ |
| PolicyApplied | `upsert()` のみ |
| HasClaims | `upsert()`, `activate()` |
| Ready | `feedback()`, `activate()` |

### TypeScript実装パターン

```typescript
// 状態をPhantom Typeで表現
type Uninitialized = { readonly _brand: "Uninitialized" };
type PolicyApplied = { readonly _brand: "PolicyApplied" };
type HasClaims = { readonly _brand: "HasClaims" };
type Ready = { readonly _brand: "Ready" };

// 状態ごとに異なるメソッドシグネチャ
interface PCEMemory<S> {
  applyPolicy(this: PCEMemory<Uninitialized>): PCEMemory<PolicyApplied>;
  upsert(this: PCEMemory<PolicyApplied>, claim: ClaimInput): PCEMemory<HasClaims>;
  upsertMore(this: PCEMemory<HasClaims>, claim: ClaimInput): PCEMemory<HasClaims>;
  activate(this: PCEMemory<HasClaims>, query: ActivateQuery): PCEMemory<Ready>;
  feedback(this: PCEMemory<Ready>, fb: FeedbackInput): PCEMemory<Ready>;
}

// ファクトリ関数
function createPCEMemory(): PCEMemory<Uninitialized>;
```

### 使用例

```typescript
// ✅ 正しい使用（コンパイル成功）
const api = createPCEMemory();
const applied = api.applyPolicy();
const hasClaims = applied.upsert({ text: "...", scope: "session" });
const ready = hasClaims.activate({ scopes: ["session"], allow: ["public"] });
ready.feedback({ claim_id: "...", signal: "helpful" });

// ❌ 不正な使用（コンパイルエラー）
api.upsert({ text: "..." });
// Error: 'this' context of type 'PCEMemory<Uninitialized>'
// is not assignable to method's 'this' of type 'PCEMemory<PolicyApplied>'
```

## 結果

### 保証される性質

| 性質 | 保証方法 |
|------|---------|
| ポリシー適用後のみupsert可能 | 型システム（コンパイル時） |
| claims存在後のみactivate可能 | 型システム（コンパイル時） |
| 不正呼び出しなし | 状態遷移の不存在 |

### トレードオフ

| メリット | デメリット |
|---------|-----------|
| コンパイル時安全性 | API複雑性の増加 |
| 実行時エラーなし | 状態管理の理解が必要 |
| 形式検証で証明済み | 動的な使用パターンに不向き |

## 参考資料

- [api_interface_verification_results.md](../spec/api_interface_verification_results.md) - 形式検証結果
- [api_statemachine.tla](../spec/tlaplus/api_designs/api_statemachine.tla) - TLA+仕様
- [api_interface_comparison.als](../spec/alloy/api_interface_comparison.als) - Alloy比較仕様
- [ADR-0001](./0001-formal-design-v1-v2-hybrid.md) - 内部設計のADR

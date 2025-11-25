# API インターフェース設計の形式検証結果

## 検証対象

3つのAPIインターフェース設計を比較検証:

| 設計 | 概要 | 特徴 |
|------|------|------|
| A: フラットAPI | 全操作がいつでも呼び出し可能 | シンプル、制約なし |
| B: ビルダーAPI | 段階的に構築、完成まで実行不可 | 順序強制、部分構築 |
| C: 状態機械API | 状態ごとに許可操作を制限 | 型安全、不正呼び出し不可 |

## Alloy検証結果

```
FlatAPI_UnsafeUpsert            SAT  ← 反例発見（安全でない）
Builder_CompleteOnlyAfterAllFields   SAT  ← 反例発見
SM_UpsertRequiresPolicy         UNSAT ← 反例なし（安全）
SM_ActivateRequiresClaims       UNSAT ← 反例なし（安全）
CompareUpsertSafety             SAT  ← 差異を発見
CompareErrorPaths               SAT  ← 差異を発見
```

### 結果の解釈

| アサーション | 結果 | 意味 |
|------------|------|------|
| FlatAPI_UnsafeUpsert | **SAT（違反）** | ポリシー未適用でupsert呼び出し可能 |
| SM_UpsertRequiresPolicy | **UNSAT（成立）** | upsertは必ずポリシー適用後 |
| SM_ActivateRequiresClaims | **UNSAT（成立）** | activateは必ずclaims存在後 |

## 設計比較サマリー

```
┌────────────────────────────────────────────────────────────────┐
│                     安全性の比較                               │
├──────────────┬──────────────┬──────────────┬──────────────────┤
│   検証項目   │ 設計A(フラット) │ 設計B(ビルダー) │ 設計C(状態機械) │
├──────────────┼──────────────┼──────────────┼──────────────────┤
│ 不正なupsert │ ❌ 可能     │ ❌ 可能      │ ✅ 不可能       │
│ 不完全ビルド │ N/A         │ ✅ 防止      │ ✅ 防止         │
│ 順序強制    │ ❌ なし     │ △ 部分的    │ ✅ 完全         │
│ エラーパス  │ ❌ 実行時   │ ❌ 実行時    │ ✅ コンパイル時  │
└──────────────┴──────────────┴──────────────┴──────────────────┘
```

## 発見された問題

### 設計A（フラットAPI）の問題

**反例**: ポリシー未適用状態でupsertが呼び出される

```
State {
  policyApplied = False,
  claims = {}
}
→ Upsert(c1) 呼び出し可能（実行時エラーになる）
```

### 設計B（ビルダーAPI）の問題

**反例**: ポリシー未適用でもbuildまで進める

```
BuilderState = HasBoundary
policyApplied = False
→ Build() 呼び出し可能（実行時エラーになる）
```

### 設計C（状態機械API）の利点

**反例なし**: 不正な呼び出しは定義されていない

```
State = Uninitialized
→ Upsert() は遷移として定義されていない
→ コンパイル時に排除される
```

## 推奨設計

### 結論: 設計C（状態機械API）を推奨

**理由**:
1. **安全性**: 不正な呼び出しがコンパイル時に排除される
2. **エラーなし**: 実行時エラーパスが存在しない
3. **型レベル保証**: TypeScriptのPhantom Typeで実装可能

### TypeScript実装例

```typescript
// 状態をPhantom Typeで表現
type Uninitialized = { readonly _brand: "Uninitialized" };
type PolicyApplied = { readonly _brand: "PolicyApplied" };
type HasClaims = { readonly _brand: "HasClaims" };
type Ready = { readonly _brand: "Ready" };

interface PCEMemory<S> {
  // Uninitializedでのみ呼び出し可能
  applyPolicy(this: PCEMemory<Uninitialized>): PCEMemory<PolicyApplied>;

  // PolicyAppliedでのみ呼び出し可能
  upsert(this: PCEMemory<PolicyApplied>, claim: ClaimInput): PCEMemory<HasClaims>;

  // HasClaimsでのみ呼び出し可能
  activate(this: PCEMemory<HasClaims>, query: Query): PCEMemory<Ready>;

  // Readyでのみ呼び出し可能
  feedback(this: PCEMemory<Ready>, fb: FeedbackInput): void;
}

// 使用例
const api = createPCEMemory(); // PCEMemory<Uninitialized>

// ✅ 正しい順序
const applied = api.applyPolicy();        // PCEMemory<PolicyApplied>
const hasClaims = applied.upsert({...});  // PCEMemory<HasClaims>
const ready = hasClaims.activate({...});  // PCEMemory<Ready>
ready.feedback({...});                    // OK

// ❌ コンパイルエラー
api.upsert({...}); // Error: 'this' context of type 'PCEMemory<Uninitialized>'
                   // is not assignable to method's 'this' of type 'PCEMemory<PolicyApplied>'
```

## 検証ファイル

- `docs/spec/tlaplus/api_designs/api_flat.tla` - 設計A TLA+仕様
- `docs/spec/tlaplus/api_designs/api_builder.tla` - 設計B TLA+仕様
- `docs/spec/tlaplus/api_designs/api_statemachine.tla` - 設計C TLA+仕様
- `docs/spec/alloy/api_interface_comparison.als` - Alloy比較仕様

# Property-based Testing Guide

このディレクトリはProperty-based Testing (PBT) のためのテンプレートとユーティリティを含みます。

## ファイル構成

- `arbitraries.ts` - fast-checkのArbitraryジェネレーター（Branded ID生成）
- `boundary.test.ts` - Boundaryモジュールのプロパティベーステスト例
- `README.md` - このファイル

## Property-based Testing とは？

Property-based Testing (PBT) は、LDE (Law-Driven Engineering) の重要な要素です。
従来のExample-based testingが具体的な入力/出力のペアをテストするのに対し、
PBTは**すべての入力に対して成り立つべき性質（不変条件）**をテストします。

### 例: Example-based vs Property-based

**Example-based**:
```typescript
test('add(2, 3) should return 5', () => {
  expect(add(2, 3)).toBe(5);
});
```

**Property-based**:
```typescript
test('Property: add is commutative', () => {
  fc.assert(
    fc.property(fc.integer(), fc.integer(), (a, b) => {
      expect(add(a, b)).toBe(add(b, a));
    })
  );
});
```

PBTは**数百～数千のランダムな入力**で不変条件を検証します。

## Arbitraries の使い方

`arbitraries.ts`はPCEのBranded Typeに対応するArbitraryを提供します。

### 基本的な使い方

```typescript
import * as fc from 'fast-check';
import { ClaimArb, BoundaryArb } from './arbitraries.js';

// Claimをランダムに生成
fc.sample(ClaimArb, 3);
// => [
//   { id: 'clm_1a2b3c', text: '...', kind: 'fact', ... },
//   { id: 'clm_4d5e6f', text: '...', kind: 'preference', ... },
//   { id: 'clm_7g8h9i', text: '...', kind: 'task', ... }
// ]

// プロパティテストで使用
test('Property: some invariant', () => {
  fc.assert(
    fc.property(ClaimArb, BoundaryArb, (claim, boundary) => {
      // テスト対象の関数を呼び出し
      const result = myFunction(claim, boundary);
      // 不変条件を検証
      expect(/* ... */).toBe(/* ... */);
    })
  );
});
```

### カスタムArbitraryの作成

```typescript
// 特定の条件を満たすClaimを生成
const PublicClaimArb = ClaimArb.filter(
  (claim) => claim.boundary_class === 'public'
);

// 複数のArbitraryを組み合わせ
const ClaimWithFeedbackArb = fc.tuple(ClaimArb, FeedbackArb);
```

## テスト命名規則

LDE原則に従い、テストには以下の命名規則を使用します：

- **Property-based test**: `"Property: <Module> - <Invariant>"`
  - 例: `"Property: Extractor - must respect boundary classes"`
- **Unit test**: `"Unit: <Module> - <Behavior>"`
  - 例: `"Unit: Boundary validation - should accept valid claim"`

## テスト実行

```bash
# すべてのテストを実行
pnpm test

# Watchモードで実行
pnpm test:watch

# Property-based testのみ実行
pnpm test:pbt
```

## 不変条件の定義

`docs/core-types.md`の各モジュールにProperty定義があります：

- **Property 6.1**: Extractor の不変条件
- **Property 6.2**: Boundary の不変条件
- **Property 7.1**: Integrator の不変条件
- **Property 8.1**: Retriever の不変条件
- **Property 9.1**: Critic の不変条件

各プロパティをテストコードに変換してください。

## fast-check のベストプラクティス

### 1. numRuns の調整

```typescript
fc.assert(fc.property(/* ... */), {
  numRuns: 200,        // デフォルトは100、重要な不変条件は200-1000
  endOnFailure: true,  // 失敗時即座に停止（デバッグが容易）
});
```

### 2. Shrinking の活用

fast-checkは失敗時に**最小の反例**を自動的に探します：

```
Property failed after 47 runs with seed=1234567890 and path="42:1:0:0":
  Counterexample: { id: 'clm_0', text: '', ... }
  Shrunk 15 times
```

### 3. Seed を使った再現

```typescript
fc.assert(fc.property(/* ... */), {
  seed: 1234567890,  // 失敗したテストを再現
  path: "42:1:0:0",  // shrinkingのパス
});
```

## Coverage 目標

LDE原則に従い、以下のカバレッジ目標を設定しています：

- **Line Coverage**: ≥ 80%
- **Branch Coverage**: ≥ 80%
- **Function Coverage**: ≥ 80%
- **Mutation Score**: ≥ 60% (optional)

```bash
# カバレッジレポート生成
pnpm test --coverage
```

## 参考資料

- [fast-check Documentation](https://fast-check.dev/)
- [Property-based Testing in Practice](https://fsharpforfunandprofit.com/pbt/)
- [docs/core-types.md](../../../docs/core-types.md) - Property定義

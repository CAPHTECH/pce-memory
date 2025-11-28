# ADR-0001: 形式検証に基づく設計選択（V1 Conservative + V2 Layer統合）

## ステータス

採択済み（2024-11-25）

## コンテキスト

PCE-Memoryシステムの設計について、形式検証（TLA+モデル検査およびAlloy構造解析）を用いて4つの設計バリアントを比較評価した。

### 評価した設計バリアント

1. **V1 Conservative**: fp-ts Either による明示的エラー処理
2. **V2 Effect-TS**: Layer依存グラフ + Scope リソース管理
3. **V3 PBT-First**: Property-Based Testing をプライマリ仕様とする
4. **V4 Hybrid**: TLA+ + SMT + Effect + Runtime Monitoring の統合

### 形式検証の結果

#### TLA+モデル検査

| バリアント | 結果                 | 発見                 |
| ---------- | -------------------- | -------------------- |
| V1         | 全不変条件パス       | エラー処理保証が堅牢 |
| V2         | **LayerAcyclic違反** | 自己依存バグ発見     |
| V3         | **Liveness違反**     | 公平性制約欠如       |
| V4         | V2バグ継承           | 複雑性コスト高       |

#### Alloy構造解析

| モデル         | アサーション          | 結果            |
| -------------- | --------------------- | --------------- |
| Either (B)     | NoStateChangeOnError  | UNSAT（成立）   |
| Effect (C)     | RequirementsSatisfied | UNSAT（成立）   |
| Bracketed (RB) | NoLeakFinal           | SAT（反例発見） |
| Scoped (RC)    | NoLeakOnExit          | SAT（反例発見） |
| Layer (DC)     | AdheresToWiring       | UNSAT（成立）   |

### 発見されたバグと問題

1. **V2 自己依存バグ**: `RegisterLayer`が`name ∈ requires`を許可（例: `DB requires {DB}`）
2. **V3 ライブネス問題**: stutteringによりカバレッジ目標到達不能
3. **リソースモデル**: 共有リソースの所有権制約欠如

## 決定

**V1（Conservative）をベースに、V2のLayer拡張を修正して統合する。**

### 設計原則

1. **エラー処理**: fp-ts `Either<Error, Success>` による明示的ハンドリング
2. **依存関係**: Layer依存グラフ（自己依存禁止ガード付き）
3. **リソース管理**: Scoped リソース（一意所有権制約付き）
4. **検証**: TLA+仕様との対応を維持

### 採用しない設計

- **V3 PBT-First**: 仕様ではなくテストオラクルとして補完的に使用
- **V4 Hybrid**: 複雑性コストが利益を上回る

## 修正点

### 1. V2 LayerAcyclic修正

```tla
\* 修正前（バグあり）
RegisterLayer(name, provides, requires) ==
  /\ DependenciesSatisfied(requires)
  /\ ...

\* 修正後
RegisterLayer(name, provides, requires) ==
  /\ name \notin requires  \* 自己依存禁止
  /\ DependenciesSatisfied(requires)
  /\ ...
```

### 2. リソース所有権制約追加

```tla
\* 追加: リソースは単一スコープにのみ所属
UniqueOwnership ==
  \A r \in UNION {scopeResources[s] : s \in ScopeId} :
    Cardinality({s \in ScopeId : r \in scopeResources[s]}) <= 1
```

### 3. TypeScript実装パターン

```typescript
// ドメイン層（V1 Conservative）: fp-ts Either
import * as E from "fp-ts/Either";
export const validateClaim = (text: string): E.Either<Error, string> => ...

// システム層（V2 Layer）: 依存グラフ
interface LayerGraph {
  registerLayer(name: string, requires: string[]): E.Either<Error, void>;
}
```

## 結果

### 保証される性質

| 性質           | 保証                                            |
| -------------- | ----------------------------------------------- |
| エラー全体性   | `lastResult ∈ {Left, Right}`                    |
| 状態一貫性     | `Left → 状態不変`                               |
| Layer非循環性  | `∀l1,l2: l1 ∈ requires(l2) ⇒ l2 ∉ requires(l1)` |
| リソース安全性 | `scope終了 → リソース解放`                      |

### 検証成果物

- TLA+仕様: `docs/spec/tlaplus/pce_v1v2_integrated.tla`
- Alloy仕様: `docs/spec/alloy/design_comparison.als`
- 検証結果: `docs/spec/verification_results.md`

## 参考資料

- [verification_results.md](../spec/verification_results.md) - 形式検証結果
- [pce_v1_conservative.tla](../spec/tlaplus/pce_v1_conservative.tla) - V1 TLA+仕様
- [pce_v2_effect.tla](../spec/tlaplus/pce_v2_effect.tla) - V2 TLA+仕様
- [design_comparison.als](../spec/alloy/design_comparison.als) - Alloy比較仕様

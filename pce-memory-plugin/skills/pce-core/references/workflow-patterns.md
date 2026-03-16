# PCE Memory Workflow Patterns

## Pattern 1: 新機能実装

```
1. activate({ q: "関連機能 設計 API", scope: ["project", "principle"] })
   → 既存の設計決定・規約を確認

2. 実装を進める（想起した知識を考慮）

3. upsert({
     text: "具体的な設計決定",
     kind: "fact",
     scope: "project",
     boundary_class: "internal"
   })
   → 新しい決定を記録

4. feedback({ claim_id: "clm_xxx", signal: "helpful" })
   → 参考になった知識にフィードバック
```

## Pattern 2: バグ修正

```
1. activate({ q: "エラーメッセージ 関連コンポーネント", scope: ["project", "session"] })
   → 過去の類似問題や関連実装を確認

2. 原因を特定して修正

3. upsert({
     text: "根本原因と解決策",
     kind: "fact",
     scope: "project"
   })
   → 解決策を記録（将来の参考に）
```

## Pattern 3: コードレビュー

```
1. activate({ q: "コーディング規約 命名 スタイル", scope: ["project", "principle"] })
   → プロジェクトの規約を確認

2. レビュー実施（規約に基づいて）

3. 新しい規約が決まったら upsert({ kind: "preference" })
```

## Pattern 4: リファクタリング

```
1. activate({ q: "アーキテクチャ パターン 依存", scope: ["project"] })
   → 現在の設計意図を確認

2. リファクタリング実施

3. upsert({
     text: "リファクタリングの理由と新しい構造",
     kind: "fact",
     scope: "project"
   })
```

## Pattern 5: 設計相談

```
1. activate({ q: "設計パターン トレードオフ", scope: ["project", "principle"] })
   → 既存の設計決定と原則を確認

2. 選択肢を比較検討

3. upsert({
     text: "選択した設計とその理由（ADR形式推奨）",
     kind: "fact",
     scope: "project"
   })
```

## Anti-patterns（やってはいけないこと）

- **全ての会話を記録する**: 重要な決定のみを厳選
- **曖昧なテキストで記録**: 「色々決めた」→「認証トークンの期限を15分に設定」
- **secretを記録する**: APIキーやパスワードは絶対に記録しない
- **feedbackを忘れる**: activateした知識の品質フィードバックは知識の精度向上に重要

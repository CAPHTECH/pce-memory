---
name: pce-core
context: fork
description: "pce-memoryの中核ワークフロー（activate/upsert/feedback）を管理するスキル。知識の想起・記録・フィードバックをガイドし、scope/kind/boundaryの適切な判断を支援する。「knowledge recall」「record to memory」「activate context」「memory workflow」「知識を想起」「記録して」「フィードバック」と言われた時に使用する。"
argument-hint: "[activate|upsert|feedback] [query or text...]"
allowed-tools: "mcp__pce-memory__pce_memory_activate, mcp__pce-memory__pce_memory_upsert, mcp__pce-memory__pce_memory_feedback, mcp__pce-memory__pce_memory_state, mcp__pce-memory__pce_memory_policy_apply, mcp__pce-memory__pce_memory_upsert_entity, mcp__pce-memory__pce_memory_upsert_relation"
---

# PCE Core - Knowledge Management Workflow

pce-memoryの中核ワークフロー（activate → 作業 → upsert → feedback）を管理する。

## 引数の解釈

`$ARGUMENTS` を解析する:
- `activate [query]` → 知識想起モード
- `upsert [kind] [text]` → 知識記録モード
- `feedback [claim-id] [signal]` → フィードバックモード
- 引数なし → ワークフロー全体のガイド

## 1. 知識想起（Activate）

関連知識をpce-memoryから取得し、作業コンテキストに注入する。

### 手順

1. `pce_memory_state` で現在の状態を確認
2. Uninitialized の場合は `pce_memory_policy_apply` を先に実行
3. `pce_memory_activate` を呼び出す:
   - `q`: ユーザーの意図からキーワードを抽出（自然言語OK）
   - `scope`: 適切なスコープを選択（[scope-boundary-guide.md](references/scope-boundary-guide.md) 参照）
   - `top_k`: 通常は 5-10
   - `allow`: 用途に応じて `["answer:task"]` や `["answer:fact"]` を指定
4. 取得した知識を要約してユーザーに提示

### activateのベストプラクティス

- クエリは具体的に: 「認証」より「JWT認証 トークン期限」の方が精度が高い
- 複数のactivateを組み合わせて網羅的に検索する
- 取得した知識が多い場合は優先度順にフィルタする

## 2. 知識記録（Upsert）

重要な決定事項や発見をpce-memoryに永続化する。

### 手順

1. 記録すべき内容を特定する
2. 適切な `kind` を選択:
   - `fact`: アーキテクチャ決定、技術的制約、API仕様
   - `preference`: コーディングスタイル、ツール選択、命名規則
   - `task`: 進行中の作業、TODO項目
   - `policy_hint`: セキュリティ要件、運用ルール
3. `scope` と `boundary_class` を決定（[scope-boundary-guide.md](references/scope-boundary-guide.md) 参照）
4. `pce_memory_upsert` を呼び出す
5. 必要に応じて `pce_memory_upsert_entity` / `pce_memory_upsert_relation` でグラフも更新

### upsertのベストプラクティス

- テキストは簡潔かつ具体的に（1-2文が理想）
- `content_hash` は必ず設定（SHA256）
- `provenance` で記録の経緯を追跡可能にする
- 過度な記録は避ける: 重要な決定のみを厳選

## 3. フィードバック（Feedback）

activateで取得した知識の品質を報告する。

### 手順

1. activateで取得した知識のclaim_idを特定
2. 適切なsignalを選択:
   - `helpful`: 問題解決に貢献した
   - `harmful`: 誤情報だった、バグの原因になった
   - `outdated`: 情報が古くなっていた
   - `duplicate`: 同じ内容が別claimに存在する
3. `pce_memory_feedback` を呼び出す

## ワークフローパターン

[workflow-patterns.md](references/workflow-patterns.md) を参照。

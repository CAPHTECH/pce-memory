---
name: pce-graph
context: fork
description: "pce-memoryのナレッジグラフ操作スキル。エンティティ・リレーションの作成・クエリ・可視化を行う。「create entity」「graph relation」「query knowledge graph」「map dependencies」「エンティティ作成」「関係を追加」「グラフ検索」と言われた時に使用する。"
argument-hint: "[entity|relation|query] [args...]"
allowed-tools: "mcp__pce-memory__pce_memory_upsert_entity, mcp__pce-memory__pce_memory_upsert_relation, mcp__pce-memory__pce_memory_query_entity, mcp__pce-memory__pce_memory_query_relation, mcp__pce-memory__pce_memory_state"
---

# PCE Graph - Knowledge Graph Operations

pce-memoryのナレッジグラフ（エンティティ・リレーション）を操作する。

## 引数の解釈

`$ARGUMENTS` を解析する:
- `entity [name] [type]` → エンティティ作成/検索
- `relation [from] [to] [type]` → リレーション作成
- `query [pattern]` → グラフ検索
- 引数なし → インタラクティブガイド

## エンティティ操作

### エンティティの作成

コードベースの重要な構成要素をエンティティとして登録する。

```
pce_memory_upsert_entity({
  id: "entity-unique-id",
  type: "component|module|api|database|service|concept",
  name: "表示名",
  properties: { ... }  // 任意の追加情報
})
```

### エンティティタイプの使い分け

[entity-relation-patterns.md](references/entity-relation-patterns.md) を参照。

| Type | 用途 | 例 |
|------|------|-----|
| component | ソフトウェアコンポーネント | AuthService, UserController |
| module | モジュール/パッケージ | pce-boundary, pce-embeddings |
| api | APIエンドポイント | POST /api/claims |
| database | データストア | DuckDB, Redis |
| service | 外部サービス | OpenAI API, GitHub |
| concept | 概念・パターン | State Machine, CRDT |

### エンティティの検索

```
pce_memory_query_entity({
  type: "component",     // タイプでフィルタ
  name_pattern: "Auth*"  // 名前パターン
})
```

## リレーション操作

### リレーションの作成

エンティティ間の関係を登録する。

```
pce_memory_upsert_relation({
  from_id: "entity-a",
  to_id: "entity-b",
  relation_type: "depends_on|implements|contains|calls|stores_in",
  properties: { ... }
})
```

### リレーションタイプの使い分け

| Type | 意味 | 例 |
|------|------|-----|
| depends_on | 依存関係 | AuthService depends_on JWTLibrary |
| implements | 実装関係 | UserController implements IUserAPI |
| contains | 包含関係 | CoreModule contains StateManager |
| calls | 呼び出し関係 | Handler calls Repository |
| stores_in | 永続化先 | ClaimStore stores_in DuckDB |

### リレーションの検索

```
pce_memory_query_relation({
  from_id: "entity-a",        // 起点でフィルタ
  relation_type: "depends_on" // タイプでフィルタ
})
```

## 典型的なワークフロー

### 依存関係マッピング

1. 主要コンポーネントをエンティティとして登録
2. コンポーネント間の依存関係をリレーションとして登録
3. `query_relation` で依存ツリーを可視化

### アーキテクチャ記録

1. レイヤー/モジュールをエンティティとして登録
2. contains/implements 関係を登録
3. claims（upsert）と連携して設計決定をエンティティに紐付け

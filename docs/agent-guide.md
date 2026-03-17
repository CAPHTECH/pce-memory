# pce-memory エージェント利用ガイド

> このファイルをプロジェクトの `CLAUDE.md` または `AGENTS.md` にコピー/参照して、AIエージェントがpce-memoryを適切に利用できるようにしてください。
>
> **P0 推奨導線**: Claude Code では [`pce-memory-plugin`](../pce-memory-plugin/README.md) を正式導線として使い、`state → policy_apply → activate → selective upsert → feedback` を自動運用してください。

---

## pce-memory とは

プロジェクトの知識（設計決定、規約、好み、タスク）を永続化し、セッションを跨いで想起するためのMCPサーバーです。

---

## 利用フロー

```
1. activate   → タスク開始前に関連知識を想起
2. 作業実行   → 想起した知識を考慮して実装
3. upsert     → 重要な決定事項を記録
4. feedback   → 知識の有用性をフィードバック
```

---

## いつ activate するか

以下の状況で `pce_memory_activate` を呼び出してください：

- **新しいタスクを開始するとき** - 関連する過去の決定を確認
- **設計判断が必要なとき** - 既存のアーキテクチャ決定を参照
- **命名や規約を確認したいとき** - プロジェクト固有のルールを想起
- **エラーに遭遇したとき** - 過去の類似問題の解決策を検索

```json
// 例: API設計前に関連知識を想起
{
  "q": "api naming convention restful",
  "scope": ["project", "principle"],
  "allow": ["answer:task"],
  "top_k": 10
}
```

---

## いつ upsert するか

以下の情報を `pce_memory_upsert` で記録してください：

### kind: fact（事実）

- アーキテクチャ決定（「認証にはJWTを使用」）
- 技術的制約（「DuckDBはFOREIGN KEY CASCADEをサポートしない」）
- API仕様（「POST /cancel は非同期で202を返す」）

### kind: preference（好み）

- コーディングスタイル（「関数型パターンを好む」）
- ツール選択（「テストにはVitestを使用」）
- 命名規則（「ハンドラは handle\* プレフィックス」）

### kind: task（タスク）

- 進行中の作業（「認証機能を実装中」）
- TODO項目（「エラーハンドリングを追加する必要がある」）

### kind: policy_hint（ポリシーヒント）

- セキュリティ要件（「PII は internal 以上で保護」）
- 運用ルール（「本番DBへの直接アクセス禁止」）

```json
// 例: 設計決定を記録
{
  "text": "Decision: use fp-ts Either for state transitions. Reason: keep errors explicit and avoid throws.",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "provenance": {
    "at": "2025-11-27T15:00:00Z",
    "actor": "claude",
    "note": "ADR-0002で決定"
  },
  "content_hash": "sha256:..."
}
```

> **運用ルール**: `activate` のクエリと `upsert` のテキストは英語で統一してください。検索一貫性と team sync を優先します。

---

## scope の使い分け

| scope       | 用途             | 例                                              |
| ----------- | ---------------- | ----------------------------------------------- |
| `session`   | 今回の会話限定   | 「このファイルを編集中」「デバッグ中の仮説」    |
| `project`   | プロジェクト固有 | 「JWTで認証」「Vitestでテスト」「REST API設計」 |
| `principle` | 普遍的原則       | 「TDDで開発」「SOLID原則を遵守」                |

---

## boundary_class の使い分け

| class      | 用途         | 例                                         |
| ---------- | ------------ | ------------------------------------------ |
| `public`   | 公開可能     | OSSライブラリの使い方、一般的な技術情報    |
| `internal` | 社内限定     | 内部API仕様、アーキテクチャ決定            |
| `pii`      | 個人情報含む | ユーザー名、メールアドレスを含む文脈       |
| `secret`   | 機密情報     | APIキー、認証情報（※記録しないことを推奨） |

---

## feedback を送るタイミング

activateで取得した知識が役立ったかを `pce_memory_feedback` で報告してください：

| signal      | いつ送るか                                |
| ----------- | ----------------------------------------- |
| `helpful`   | 提案/知識が採用された、問題解決に貢献した |
| `harmful`   | 提案が誤っていた、バグの原因になった      |
| `outdated`  | 情報が古くなっていた、現状と異なる        |
| `duplicate` | 同じ内容が既に別のClaimで存在する         |

```json
// 例: 知識が役立った
{
  "claim_id": "clm_abc123",
  "signal": "helpful"
}
```

---

## 実践的なワークフロー例

### 1. 新機能実装

```
User: "ユーザー認証機能を実装して"

Agent:
1. activate({ q: "auth jwt session", scope: ["project"], allow: ["answer:task"] })
   → 既存の認証関連の決定を確認

2. 実装を進める（想起した知識を考慮）

3. upsert({
     text: "Decision: auth tokens expire in 15 minutes and refresh tokens expire in 7 days.",
     kind: "fact",
     scope: "project"
   })
   → 新しい決定を記録

4. feedback({ claim_id: "clm_xxx", signal: "helpful" })
   → 参考になった知識にフィードバック
```

### 2. バグ修正

```
User: "ログインできないバグを直して"

Agent:
1. activate({ q: "login auth error", scope: ["project", "session"], allow: ["answer:task"] })
   → 過去の類似問題や関連実装を確認

2. 原因を特定して修正

3. upsert({
     text: "Root cause: JWT timezone mismatch caused login failure. Fix: normalize all token timestamps to UTC.",
     kind: "fact",
     scope: "project"
   })
   → 解決策を記録（将来の参考に）
```

### 3. コードレビュー

```
Agent:
1. activate({ q: "coding convention naming style", scope: ["project", "principle"], allow: ["answer:task"] })
   → プロジェクトの規約を確認

2. レビュー実施（規約に基づいて）

3. 新しい規約が決まったら upsert
```

---

## 注意事項

- **secret は記録しない**: APIキー、パスワード等は upsert しないでください
- **content_hash は必須**: 重複防止のため、テキストのSHA256ハッシュを含めてください
- **provenance を明記**: いつ、誰が、なぜその知識を記録したか追跡可能にしてください
- **過度な記録は避ける**: 全ての会話を記録するのではなく、重要な決定のみを厳選してください
- **completed task は新規 task claim にしない**: 完了したタスクは `feedback(outdated)` で閉じ、成果だけを `fact/preference` として残してください

---

## Graph Memoryでタグを実現する

専用のタグ機能はありませんが、Graph Memory（Entity + Relation）で代替できます。

### 1. タグをEntityとして登録

```json
// pce_memory_upsert_entity
{
  "id": "tag_typescript",
  "type": "Concept",
  "name": "TypeScript"
}
```

### 2. ClaimとタグをRelationで紐付け

```json
// pce_memory_upsert_relation
{
  "id": "rel_clm_tag_001",
  "src_id": "clm_abc123",
  "dst_id": "tag_typescript",
  "type": "TAGGED"
}
```

### 3. upsert時にentitiesとrelationsを同時登録

```json
// pce_memory_upsert（一括登録）
{
  "text": "TypeScriptのexactOptionalPropertyTypesに注意",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "content_hash": "sha256:...",
  "provenance": { "at": "2025-11-28T00:00:00Z" },
  "entities": [{ "id": "tag_typescript", "type": "Concept", "name": "TypeScript" }],
  "relations": [
    { "id": "rel_001", "src_id": "$claim_id", "dst_id": "tag_typescript", "type": "TAGGED" }
  ]
}
```

> **Note**: 既存の分類（`kind` 4種 + `scope` 3層）と `activate` の `q` パラメータによるテキスト検索で多くのケースは対応可能です。

---

## MCP設定例（Claude Desktop）

```json
{
  "mcpServers": {
    "pce-memory": {
      "command": "node",
      "args": ["/path/to/pce-memory/dist/index.js"],
      "env": {
        "PCE_DB": "/path/to/memory.duckdb"
      }
    }
  }
}
```

---

## 関連ドキュメント

- [mcp-tools.md](./mcp-tools.md) - MCP API仕様
- [ADR-0004](./adr/0004-hybrid-search-design.md) - Hybrid Search設計

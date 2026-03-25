## pce-memory とは

プロジェクトの知識（設計決定、規約、好み、タスク）を永続化し、セッションを跨いで想起するためのMCPサーバーです。

---

## 利用フロー

```
1. activate   → タスク開始前に intent-aware な想起を行う
2. observe    → 会話ログ・作業メモ・機密を raw micro memory として一時記録
3. distill    → raw 観測を durable 候補に蒸留
4. promote    → reviewable candidate を meso/macro memory に昇格
5. feedback   → 想起した知識の有用性をフィードバック
6. rollback   → 無効になった durable memory を append-only で修復
```

`upsert` は **already-distilled な durable knowledge の escape hatch** としてのみ使ってください。通常の raw -> durable 変換経路では使いません。

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
  "intent": "design_decision",
  "q": "API 命名規約 RESTful",
  "scope": ["project", "principle"],
  "kind_filter": ["fact", "preference", "policy_hint"],
  "memory_type_filter": ["knowledge", "procedure", "norm"],
  "allow": ["answer:task"],
  "top_k": 10
}
```

---

## いつ observe するか

以下の情報は `pce_memory_observe` で記録してください：

- **session スコープの作業文脈** - 「このファイルを編集中」「デバッグ中の仮説」
- **生ログや一時メモ** - チャット断片、ツール出力、HTTPレスポンス、ファイル読み取り結果
- **secret/PII を含む可能性がある内容** - fail-safe に一時保存し、durable claim 化しない

```json
// 例: セッション作業メモを一時記録
{
  "source_type": "chat",
  "content": "Issue #65 の observe 互換経路を削除中"
}
```

補足:

- `observe` は raw-only です。durable claim を inline で作成しません
- `single_claim_v0` のような旧 extraction mode は使いません
- `extract: { \"mode\": \"noop\" }` は互換性のために残っていても raw-only のままです
- durable 化したい場合は `distill -> promote` を使ってください

---

## いつ upsert するか

以下の情報だけを `pce_memory_upsert` で記録してください：

- すでに distill 済みとみなせる durable knowledge
- `project` または `principle` に置くべき確定事項
- provenance を付けて追跡可能にしたい事実・好み・手順・ポリシー
- 技術・ファイル・概念の関係が明確な場合は、`entities` / `relations` も同じ `upsert` に含めてください

補足:

- `entities` の典型例: technologies, files, modules, concepts
- `relations` の典型例: `USES`, `IMPLEMENTS`, `DEPENDS_ON`
- MCPサーバー側で自動抽出される前提にしないでください。必要な graph 情報はクライアントが明示します

### kind: fact（事実）

- アーキテクチャ決定（「認証にはJWTを使用」）
- 技術的制約（「DuckDBはFOREIGN KEY CASCADEをサポートしない」）
- API仕様（「POST /cancel は非同期で202を返す」）

### kind: preference（好み）

- コーディングスタイル（「関数型パターンを好む」）
- ツール選択（「テストにはVitestを使用」）
- 命名規則（「ハンドラは handle\* プレフィックス」）

### kind: task（タスク）

- プロジェクト横断で再利用したい作業状態（「認証機能の移行は段階リリース前提」）
- durable に残すべき TODO/運用メモ（「エラーハンドリング追加は次リリースの前提条件」）

### kind: policy_hint（ポリシーヒント）

- セキュリティ要件（「PII は internal 以上で保護」）
- 運用ルール（「本番DBへの直接アクセス禁止」）

```json
// 例: 設計決定を記録
{
  "text": "状態管理にはfp-tsのEitherを使用し、例外をthrowしない",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "memory_type": "knowledge",
  "provenance": {
    "at": "2025-11-27T15:00:00Z",
    "actor": "claude",
    "note": "ADR-0002で決定"
  },
  "content_hash": "sha256:...",
  "entities": [
    {
      "id": "ent_fp_ts",
      "type": "Artifact",
      "name": "fp-ts",
      "canonical_key": "fp-ts"
    },
    {
      "id": "ent_either",
      "type": "Concept",
      "name": "Either",
      "canonical_key": "either"
    }
  ],
  "relations": [
    {
      "id": "rel_fp_ts_implements_either",
      "src_id": "ent_fp_ts",
      "dst_id": "ent_either",
      "type": "IMPLEMENTS"
    }
  ]
}
```

---

## scope の使い分け

| scope       | 用途             | 例                                                        |
| ----------- | ---------------- | --------------------------------------------------------- |
| `session`   | 今回の会話限定   | **durable canonical memory にはしない**。`observe` を使う |
| `project`   | プロジェクト固有 | 「JWTで認証」「Vitestでテスト」「REST API設計」           |
| `principle` | 普遍的原則       | 「TDDで開発」「SOLID原則を遵守」                          |

---

## boundary_class の使い分け

| class      | 用途         | 例                                                           |
| ---------- | ------------ | ------------------------------------------------------------ |
| `public`   | 公開可能     | OSSライブラリの使い方、一般的な技術情報                      |
| `internal` | 社内限定     | 内部API仕様、アーキテクチャ決定                              |
| `pii`      | 個人情報含む | ユーザー名、メールアドレスを含む文脈                         |
| `secret`   | 機密情報     | APIキー、認証情報（**`upsert` では拒否**。`observe` を使用） |

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
1. activate({
     intent: "design_decision",
     q: "認証 JWT セッション",
     scope: ["project", "principle"],
     kind_filter: ["fact", "policy_hint"],
     memory_type_filter: ["knowledge", "procedure", "norm"],
     allow: ["answer:task"]
   })
   → 既存の認証関連の決定を確認

2. 実装を進める（想起した知識を考慮）

3. observe({
     source_type: "chat",
     content: "認証トークンは15分、リフレッシュトークンは7日で確定",
     boundary_class: "internal"
   })
   → raw decision memo を記録

4. distill({
     source_observation_ids: ["obs_xxx"],
     proposed_kind: "fact",
     proposed_scope: "project",
     proposed_memory_type: "knowledge"
   })
   → durable candidate を作成

5. promote({
     candidate_id: "pq_xxx",
     provenance: { "at": "2025-11-27T15:00:00Z", "actor": "claude" }
   })
   → 新しい決定を記録

6. feedback({ claim_id: "clm_xxx", signal: "helpful" })
   → 参考になった知識にフィードバック
```

### 2. バグ修正

```
User: "ログインできないバグを直して"

Agent:
1. activate({
     intent: "debug_incident",
     q: "ログイン 認証 エラー",
     scope: ["project"],
     memory_type_filter: ["working_state", "knowledge", "procedure"],
     include_observations: true,
     allow: ["answer:task"]
   })
   → 過去の類似問題、手順、短期の観測を確認

2. 原因を特定して修正

3. observe({
     source_type: "chat",
     content: "JWTのtimezone不一致でログイン失敗。UTC統一で再現を止めた",
     boundary_class: "internal"
   })
   → セッション文脈を一時記録

4. distill({
     source_observation_ids: ["obs_xxx"],
     proposed_kind: "fact",
     proposed_scope: "project",
     proposed_memory_type: "knowledge"
   })
   → durable candidate を作成

5. promote({
     candidate_id: "pq_xxx",
     provenance: { "at": "2025-11-27T15:30:00Z", "actor": "claude" }
   })
   → 解決策を記録（将来の参考に）
```

### 3. コードレビュー

```
Agent:
1. activate({
     intent: "design_decision",
     q: "コーディング規約 命名 スタイル",
     scope: ["project", "principle"],
     memory_type_filter: ["knowledge", "procedure", "norm"],
     allow: ["answer:task"]
   })
   → プロジェクトの規約を確認

2. レビュー実施（規約に基づいて）

3. 新しい規約が durable に残す価値を持つなら distill/promote（または reviewed upsert）
```

---

## 注意事項

- **secret は upsert しない**: APIキー、パスワード等は durable claim にせず、必要なら observe で最小限に扱ってください
- **session は upsert しない**: 現在の作業状態や一時メモは observe に残してください
- **content_hash は必須**: 重複防止のため、テキストのSHA256ハッシュを含めてください
- **provenance を明記**: いつ、誰が、なぜその知識を記録したか追跡可能にしてください
- **過度な記録は避ける**: 全ての会話を記録するのではなく、重要な決定のみを厳選してください

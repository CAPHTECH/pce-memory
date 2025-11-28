# pce-memory MCP Tools Spec v0.1

> **目的**: IDE/コードエージェント（Codex / Claude Code / Cursor 等）が **MCP（Model Context Protocol）** 経由で pce-memory を利用できるようにする最小〜完全仕様。  
> **対象**: エージェント開発者・Ops・セキュリティ。

---

## 0. Overview

- **提供形態**: MCP Server（HTTP/WS 不問）。
- **Auth**: Bearer Token（`Authorization: Bearer <token>`）/ ローカル開発は `none` 許可可。
- **Timeout**: 既定 10s（ツールごとに後述）。
- **Payload 上限**: 既定 64KB（ツールごとに後述）。
- **応答**: すべての成功レスポンスは **`policy_version`** と **`provenance`**（可能な範囲）を含める。
- **Idempotency**: `upsert` は **content_hash** で冪等。`feedback` は `(claim_id, ts_bucket)` で冪等。
- **Logging**: すべての呼び出しは append-only 監査ログに記録（時刻・呼出・境界判定・由来）。
- **Scoring / Retrieval**: `pce.memory.activate` / `pce.memory.search` は **policy (`retrieval.*`)** を読み取り、ハイブリッド結合（`alpha/k_*`）と再ランク（`use_quality`/`recency`）を適用する。スコアは `activation-ranking.md` の定義に従い **[0,1] 正規化**され、`score` は最終スコア（`combined*g`）を表す。必要に応じて詳細内訳は `include_meta:true` で返す。

---

## 1. 共通

- **Scopes**: `session | project | principle`（PCEペース層）
- **Allow tags**: 例 `answer:task`, `tool:*`, `tool:contact-lookup` など（Policy 参照）。
- **Errors**: 共通エラー語彙は §6 参照。HTTP ステータスに合わせて `code` を返す。

### 1.x Response Envelope & Tracing

- 成功応答の外形：
  `{"data": <payload>, "policy_version":"<semver>", "request_id":"<uuid>", "trace_id":"<uuid>"}`
- 失敗応答（HTTP 4xx/5xx とともに）：
  共通エラーフォーマット：

```
{"error":{"code":"<CODE>","message":"...","details":{...}}, "request_id":"<uuid>", "trace_id":"<uuid>", "policy_version":"<semver>"}
```

実装で使用中のコード一覧（詳細は docs/mcp-tools-errors.md 参照）：

| code             | 意味                                |
| ---------------- | ----------------------------------- |
| POLICY_INVALID   | policy.apply 失敗                   |
| VALIDATION_ERROR | 入力不足・型不一致                  |
| UPSERT_FAILED    | upsert 実行エラー                   |
| ACTIVATE_FAILED  | activate 実行エラー                 |
| BOUNDARY_ERROR   | boundary.validate 実行エラー        |
| BOUNDARY_DENIED  | allow/scope 不一致（allowed=false） |
| FEEDBACK_FAILED  | feedback 実行エラー                 |
| RATE_LIMIT       | レート上限超過                      |
| POLICY_MISSING   | policy 未適用（未実装だが予約）     |
| DUPLICATE        | content_hash 重複（未実装だが予約） |

### 1.y Provenance Common Schema

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "at": { "type": "string", "format": "date-time" },
    "actor": { "type": "string" },
    "git": {
      "type": "object",
      "additionalProperties": false,
      "properties": {
        "commit": { "type": "string", "pattern": "^[0-9a-f]{7,40}$" },
        "repo": { "type": "string" },
        "url": { "type": "string", "format": "uri" },
        "files": { "type": "array", "items": { "type": "string" } }
      }
    },
    "url": { "type": "string", "format": "uri" },
    "note": { "type": "string" },
    "signed": { "type": "boolean" }
  },
  "required": ["at"]
}
```

### 1.z Content Hash Normalization

- 生成前に UTF-8 / NFC・改行 CRLF→LF・先頭末尾空白除去・連続空白の圧縮を行う。
- 形式: `sha256:<hex64>`

---

## 2. Tools

### 2.1 `pce.memory.activate`

**目的**: クエリとポリシーに基づき **アクティブコンテキスト（AC）** を構成（関数 `r(q, C^L, B, policy, critic)`）。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "q": { "type": "string" },
    "scope": { "type": "array", "items": { "enum": ["session", "project", "principle"] } },
    "allow": { "type": "array", "items": { "type": "string" } },
    "top_k": { "type": "integer", "minimum": 1, "maximum": 50 },
    "cursor": { "type": "string" },
    "include_meta": { "type": "boolean", "default": false }
  },
  "required": ["q"]
}
```

- **Response Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "active_context_id": { "type": "string", "pattern": "^ac_[A-Za-z0-9]+$" },
    "claims": {
      "type": "array",
      "items": { "$ref": "#/definitions/scored_item" }
    },
    "claims_count": { "type": "integer", "minimum": 0 },
    "expires_at": { "type": "string", "format": "date-time" },
    "next_cursor": { "type": "string" },
    "has_more": { "type": "boolean" },
    "policy_version": { "type": "string" },
    "provenance": { "type": "array", "items": { "type": "object" } },
    "scoring_params": {
      "type": "object",
      "additionalProperties": false,
      "properties": {
        "alpha": { "type": "number" },
        "k_txt": { "type": "integer" },
        "k_vec": { "type": "integer" },
        "k_final": { "type": "integer" },
        "rerank": {
          "type": "object",
          "additionalProperties": false,
          "properties": {
            "use_quality": { "type": "boolean" },
            "recency_half_life_days": { "type": "number" }
          }
        }
      }
    }
  },
  "required": ["active_context_id", "claims", "policy_version"]
}
```

※ 期限切れ AC 参照時は 410 Gone を返す。

- **Timeout**: 15s / **Payload**: 16KB / **Idempotency**: safe
- **Errors**: `POLICY_MISSING`, `INVALID_SCOPE`
- **Example**

```json
// req
{"q":"解約APIの命名規約","scope":["project"],"allow":["answer:task"],"top_k":12}
// resp
{"active_context_id":"ac_9x","claims":[{"text":"POST /subscriptions/{id}/cancel は非同期"}],"policy_version":"0.1.3"}
```

---

### 2.2 `pce.memory.search`

**目的**: 既知の前提・規約・禁止事項を想起（AC の取得無し）。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "query": { "type": "string" },
    "top_k": { "type": "integer", "minimum": 1, "maximum": 50 },
    "scope": { "type": "array", "items": { "enum": ["session", "project", "principle"] } },
    "allow": { "type": "array", "items": { "type": "string" } },
    "cursor": { "type": "string" },
    "include_meta": { "type": "boolean", "default": false }
  },
  "required": ["query"]
}
```

- **Response Schema（配列要素）**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "items": { "type": "array", "items": { "$ref": "#/definitions/scored_item" } },
    "next_cursor": { "type": "string" },
    "has_more": { "type": "boolean" },
    "policy_version": { "type": "string" }
  },
  "required": ["items", "policy_version"]
}
```

※ 並びは score 降順（同点は created_at 降順）。

- **Timeout**: 10s / **Payload**: 32KB / **Idempotency**: safe
- **Errors**: `BOUNDARY_DENIED`, `RATE_LIMIT`

---

### 2.3 `pce.memory.upsert`

**目的**: 重要な断片（Observation/Claim/Graph）を登録。**由来（provenance）必須**。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "text": { "type": "string" },
    "kind": { "enum": ["fact", "preference", "task", "policy_hint"] },
    "scope": { "enum": ["session", "project", "principle"] },
    "boundary_class": { "enum": ["public", "internal", "pii", "secret"] },
    "entities": { "type": "array", "items": { "$ref": "#/definitions/entity" } },
    "relations": { "type": "array", "items": { "$ref": "#/definitions/relation" } },
    "provenance": { "$ref": "#/definitions/provenance" },
    "content_hash": { "type": "string", "pattern": "^sha256:[0-9a-f]{64}$" }
  },
  "required": ["text", "provenance"]
}
```

- **Response Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "id": { "type": "string", "pattern": "^clm_[A-Za-z0-9]+$" },
    "policy_version": { "type": "string" }
  },
  "required": ["id", "policy_version"]
}
```

- **definitions.entity**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "id": { "type": "string" },
    "type": { "enum": ["Actor", "Artifact", "Event", "Concept"] },
    "name": { "type": "string" },
    "canonical_key": { "type": "string" },
    "attrs": { "type": "object" }
  },
  "required": ["id", "type", "name"]
}
```

- **definitions.relation**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "id": { "type": "string" },
    "src_id": { "type": "string" },
    "dst_id": { "type": "string" },
    "type": { "type": "string" },
    "props": { "type": "object" },
    "evidence_claim_id": { "type": "string" }
  },
  "required": ["id", "src_id", "dst_id", "type"]
}
```

- **Timeout**: 10s / **Payload**: 64KB / **Idempotency**: `content_hash`
- **Errors**: `DUPLICATE`, `INVALID_BOUNDARY`
- **Example**

```json
// req
{"text":"Stripe webhookは10分ドリフトを許容","kind":"fact","scope":"project","boundary_class":"internal","provenance":{"git":{"commit":"abc123"}},"content_hash":"sha256:..."}
// resp
{"id":"clm_7k","policy_version":"0.1.3"}
```

---

### 2.4 `pce.memory.feedback`

**目的**: 採用/棄却/陳腐化/重複のシグナルで Critic を更新。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "claim_id": { "type": "string" },
    "signal": { "enum": ["helpful", "harmful", "outdated", "duplicate"] },
    "score": { "type": "number", "minimum": -1, "maximum": 1 }
  },
  "required": ["claim_id", "signal"]
}
```

- **Response Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": { "ok": { "type": "boolean" }, "policy_version": { "type": "string" } },
  "required": ["ok", "policy_version"]
}
```

- **Timeout**: 3s / **Payload**: 4KB / **Idempotency**: `(claim_id, ts_bucket)`
- **Errors**: `UNKNOWN_CLAIM`

---

### 2.5 `pce.memory.boundary.validate`

**目的**: 生成前に境界チェック／**Redact-before-Send**。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "payload": { "type": "string" },
    "allow": { "type": "array", "items": { "type": "string" } },
    "scope": { "enum": ["session", "project", "principle"] }
  },
  "required": ["payload"]
}
```

- **Response Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "allowed": { "type": "boolean" },
    "reason": { "type": "string" },
    "redacted": { "type": "string" },
    "policy_version": { "type": "string" }
  },
  "required": ["allowed", "policy_version"]
}
```

- **Timeout**: 5s / **Payload**: 32KB / **Idempotency**: safe
- **Errors**: `BOUNDARY_DENIED`

---

### 2.6 `pce.memory.policy.apply`

**目的**: ポリシーの適用（不変量・用途タグ・redact ルール）。**GitOps 承認推奨**。

- **Request Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "yaml": { "type": "string" },
    "dry_run": { "type": "boolean" },
    "validate_only": { "type": "boolean" },
    "expected_version": { "type": "string" },
    "signature": { "type": "string" },
    "approver": { "type": "string" }
  },
  "required": ["yaml"]
}
```

- **Response Schema**

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": { "version": { "type": "string" } },
  "required": ["version"]
}
```

- **Timeout**: 10s / **Payload**: 128KB / **Idempotency**: versioned（非冪等）
- **Errors**: `UNAUTHORIZED`, `INVALID_POLICY`

**Example (apply policy with retrieval params)**

```json
{
  "yaml": "\n# policy with retrieval parameters\nversion: 0.1\nscopes:\n  session:   { ttl: '7d',    max_tokens: 20000 }\n  project:   { ttl: '120d',  max_tokens: 50000 }\n  principle: { ttl: 'inf',   max_tokens: 100000 }\nboundary_classes:\n  public:   { allow: ['*'] }\n  internal: { allow: ['answer:task','tool:*'] }\n  pii:      { allow: ['tool:contact-lookup'], redact: ['email','phone'], escalation: 'human_review' }\n  secret:   { allow: [], escalation: 'deny' }\nretrieval:\n  hybrid:\n    alpha: 0.65\n    k_txt: 48\n    k_vec: 96\n    k_final: 12\n  rerank:\n    use_quality: false\n    recency_half_life_days: 30\n    recency:\n      half_life_days_by_kind:\n        fact: 120\n        task: 14\n        preference: 90\n        policy_hint: 365\n"
}
```

---

## 3. Versioning & Breaking Changes

- **SemVer**: `MAJOR.MINOR.PATCH`。`MAJOR` の増加時のみ破壊的変更可。
- **Tool追加**: MINOR で追加、既存の schema 変更は避ける。
- **Deprecated**: 2 リリース前に告知し、`deprecation_date` を manifest に付加。

---

## 4. セキュリティ

- **Boundary-First**: すべての検索/生成前に境界で前置フィルタ。
- **Redact-before-Send**: 外部APIに送出する前に PII/Secret をマスク。
- **Fail-closed**: policy 未読込・署名不正は拒否で応答。
- **Rate Limit**: 429 を返す。`Retry-After` を付与。
- **Rate Limit ヘッダ**: 応答に `X-RateLimit-Limit, X-RateLimit-Remaining, X-RateLimit-Reset` を付与。429 時は `Retry-After`（秒）。クライアントは指数バックオフ＋ジッタで再試行。

---

## 5. サンプル・フロー（IDE 連携）

1. `activate` で AC を取得し、プロンプト先頭に貼付。
2. 生成前に `boundary.validate` → `allowed=false` なら redact を利用。
3. 実装後、決定事項を `upsert`。
4. マージ/採用時に `feedback` を送信。

---

## 6. エラー語彙（Error Codes）

| code            | HTTP | 意味                        | 典型的対処                           |
| --------------- | ---- | --------------------------- | ------------------------------------ | ------- | ----------------- |
| BOUNDARY_DENIED | 403  | 境界/権限違反               | scope/allow を見直す / redact を適用 |
| INVALID_SCOPE   | 422  | 入力不正                    | scope を `session                    | project | principle` に修正 |
| DUPLICATE       | 409  | 競合（重複）                | 既存 ID を返す or 更新に切替         |
| UNKNOWN_CLAIM   | 404  | 参照なし                    | id を確認／再検索                    |
| POLICY_MISSING  | 424  | 依存未満足（要 policy）     | `policy.apply` を実行                |
| INVALID_POLICY  | 422  | policy YAML 構文/検証エラー | スキーマ検証を通す                   |
| RATE_LIMIT      | 429  | レート制限                  | `Retry-After` に従って再試行         |
| UNAUTHORIZED    | 401  | 認可なし                    | トークン発行／権限付与               |
| INTERNAL        | 500  | 予期しない失敗              | 再試行／問い合わせ                   |

---

## 7. 変更履歴

- **v0.1**: 初版（activate/search/upsert/feedback/boundary.validate/policy.apply）。

#### definitions.scored_item

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "claim": { "$ref": "#/definitions/claim" },
    "score": { "type": "number" },
    "scores": { "$ref": "#/definitions/scoring" },
    "evidences": { "type": "array", "items": { "$ref": "#/definitions/evidence" } },
    "reason": { "type": "string" }
  },
  "required": ["claim", "score"]
}
```

#### definitions.claim

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "id": { "type": "string" },
    "text": { "type": "string" },
    "kind": { "enum": ["fact", "preference", "task", "policy_hint"] },
    "scope": { "enum": ["session", "project", "principle"] },
    "boundary_class": { "enum": ["public", "internal", "pii", "secret"] },
    "created_at": { "type": "string", "format": "date-time" },
    "updated_at": { "type": "string", "format": "date-time" }
  },
  "required": ["id", "text", "kind", "scope", "boundary_class", "created_at", "updated_at"]
}
```

#### definitions.scoring

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "text": { "type": "number" },
    "vector": { "type": "number" },
    "combined": { "type": "number" },
    "utility": { "type": "number" },
    "confidence": { "type": "number" },
    "quality": { "type": "number" },
    "recency": { "type": "number" },
    "g": { "type": "number" }
  }
}
```

#### definitions.evidence

```json
{
  "type": "object",
  "additionalProperties": true,
  "properties": {
    "id": { "type": "string" },
    "source_type": { "type": "string" },
    "source_id": { "type": "string" },
    "snippet": { "type": "string" },
    "at": { "type": "string", "format": "date-time" }
  }
}
```

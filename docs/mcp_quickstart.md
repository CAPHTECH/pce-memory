# MCP Quickstart — pce-memory を 5 分で動かす

> **ゴール**：IDE/コードエージェントから **MCP** 経由で pce-memory を呼び、  
> `activate → boundary.validate → upsert → feedback` の **E2E** を一度まわす。
>
> **デフォルト**：常駐サーバ不要の **stdio** トランスポート（必要時に子プロセス起動）。HTTP/WS は付録を参照。

## 推奨 P0 導線: Claude Code plugin

P0 では [`pce-memory-plugin`](../pce-memory-plugin/README.md) を正式導線とします。plugin が state guard と activate-first の運用を固定します。

```bash
claude --plugin-dir ./pce-memory-plugin
```

plugin 同梱の `.mcp.json` は `npx -y pce-memory@latest` を使用します。

## 代替: 手動 MCP セットアップ

```bash
mkdir -p ~/.pce/manual-demo
```

---

## 0. 事前準備（1 分）

- **トークン**：`PCE_TOKEN="<your-token>"`
- **ポリシー**：まずは最小ポリシーを適用します（Redact-before-Send / Fail-closed）。

```yaml
# policy/base.yaml（最小）
version: 0.1
scopes: { session: { ttl: '7d' }, project: { ttl: '120d' }, principle: { ttl: 'inf' } }
boundary_classes:
  public: { allow: ['*'] }
  internal: { allow: ['answer:task', 'tool:*'] }
  pii: { allow: ['tool:contact-lookup'], redact: ['email', 'phone'], escalation: 'human_review' }
  secret: { allow: [], escalation: 'deny' }
```

> ポリシーの詳細は `boundary-policy.md` を参照。

---

## 1. 起動（stdio：デフォルト・常駐なし）

通常は **IDE/エージェントが必要時に子プロセスとして起動**するため、手動起動は不要です。

> 手動で動作確認したい場合のみ：
>
> ```bash
> PCE_TOKEN="<your-token>" PCE_POLICY="/path/to/policy/base.yaml" \
> npx -y pce-memory@latest
> ```

---

## 2. MCP クライアント（IDE/エージェント）を接続（1 分）

### 2.1 Cursor（例）

- Cursor の MCP 設定で以下を追加（参考）：

```json
{
  "servers": {
    "pce-memory": {
      "type": "stdio",
      "command": "npx",
      "args": ["-y", "pce-memory@latest"],
      "env": {
        "PCE_TOKEN": "${PCE_TOKEN}",
        "PCE_POLICY": "/absolute/path/to/policy/base.yaml"
      }
    }
  }
}
```

> 実際の UI/設定ファイル名はバージョンにより異なります。エージェント側で **MCP Manifest** を認識し、ツールが列挙されれば接続成功。

### 2.2 Claude Code / Codex（例）

- Claude Code は plugin 導線を推奨:

```bash
claude --plugin-dir ./pce-memory-plugin
```

- 手動登録する場合は **stdio** サーバを追加:

```json
{
  "mcpServers": {
    "pce-memory": {
      "command": "npx",
      "args": ["-y", "pce-memory@latest"]
    }
  }
}
```

- ツール一覧に `pce_memory_*` が見えたら OK。

---

## 3. E2E：activate → validate → upsert → feedback（2 分）

> IDE/エージェントの **MCP ツール実行UI** から、下記の JSON を順に送ってください（ツール名は `mcp-tools.md` に準拠）。

### 3.1 policy.apply（最初だけ）

**ツール**：`pce_memory_policy_apply`  
**Payload**：

```json
{
  "yaml": "version: 0.1\nscopes:\n  session: { ttl: '7d' }\n  project: { ttl: '120d' }\n  principle: { ttl: 'inf' }\nboundary_classes:\n  public:   { allow: ['*'] }\n  internal: { allow: ['answer:task','tool:*'] }\n  pii:      { allow: ['tool:contact-lookup'], redact: ['email','phone'], escalation: 'human_review' }\n  secret:   { allow: [], escalation: 'deny' }\n"
}
```

期待：`data.version` が返る（Response Envelope 参照）。

### 3.2 upsert（既知の前提を 2 件登録）

**ツール**：`pce_memory_upsert`  
**Payload 例**：

```json
{
  "text": "解約APIは POST /subscriptions/{id}/cancel（非同期・冪等）",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "provenance": { "git": { "commit": "abc123", "repo": "org/repo" } },
  "content_hash": "sha256:1d..."
}
```

### 3.3 activate（AC を構成し、前提をまとめて取得）

**ツール**：`pce_memory_activate`  
**Payload**：

```json
{ "q": "解約/返金 仕様", "scope": ["project"], "allow": ["answer:task"], "top_k": 12 }
```

期待：`data.active_context_id` と `claims[]` が返る。

### 3.4 boundary.validate（生成前チェック＆マスク）

**ツール**：`pce_memory_boundary_validate`  
**Payload**：

```json
{ "payload": "連絡は ryo@example.com へ", "allow": ["answer:task"], "scope": "project" }
```

期待：`data.allowed=true` と `data.redacted` が返る。

### 3.5 feedback（採用/棄却を学習）

**ツール**：`pce_memory_feedback`  
**Payload**：

```json
{ "claim_id": "clm_7k", "signal": "helpful", "score": 1.0 }
```

---

## 4. エージェント連携のベストプラクティス

1. **Activation → Prompt 前置**：`activate` で返った claims を“前提”として最上流に貼る。
2. **必ず validate**：生成の前後で `boundary.validate`。`allowed=false` は必ず redraft/redact。
3. **Provenance を義務化**：`upsert` は `provenance` 必須。Git/URL/署名のいずれかを付ける。
4. **feedback を返す**：採用/棄却を `feedback` で送る（Critic 学習 → 次回の再ランクに反映）。
5. **再 activate を前提にする**：新タスク開始時、context compaction 後、または recalled knowledge が会話から落ちた後は再 `activate`。

---

## 5. よくあるエラーと対処

| 症状              | 典型エラー              | 対処                                                        |
| ----------------- | ----------------------- | ----------------------------------------------------------- |
| AC が取得できない | `STATE_ERROR`           | `pce_memory_state` を確認し、必要なら `policy.apply` を実行 |
| 想起が拒否される  | `BOUNDARY_DENIED` / 0件 | `scope/allow` を見直す・`boundary.validate` で redaction    |
| upsert が重複気味 | `is_new: false`         | 同じ内容の既存 claim を再利用し、新規乱立を避ける            |
| レート制限        | `RATE_LIMIT`            | 短時間の連続呼び出しを避け、再試行する                       |

---

## 6. 片付け（任意）

- 作業 AC は必要時に再 `activate` する。P0 では自動再構成を前提にし、明示的 invalidate は前提にしない。
- 監査ログを確認：`request_id/trace_id/policy_version` で関連呼び出しを相関。

---

## 付録 A：MCP Manifest（参考）

```json
{
  "name": "pce-memory",
  "version": "0.1.0",
  "tools": [
    { "name": "pce_memory_activate" },
    { "name": "pce_memory_upsert" },
    { "name": "pce_memory_feedback" },
    { "name": "pce_memory_boundary_validate" },
    { "name": "pce_memory_policy_apply" }
  ]
}
```

> 仕様の詳細は `mcp-tools.md`、ポリシーは `boundary-policy.md`、PCE の背景は `pce.ja.md / pce-model.ja.md` を参照。

---

## 付録 B：HTTP 実装の参考コマンド（任意）

> HTTP/WS 実装で試したい場合のみ。stdio が既定です。

### policy.apply（最初だけ）

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_policy_apply \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d @<(cat <<'JSON'
{"yaml":"$(python3 - <<'PY'
import sys, json
print(open('policy/base.yaml').read().replace('\n','\\n').replace('"','\\"'))
PY
)"}
JSON
)
```

### upsert（既知の前提を 2 件登録）

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_upsert \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d '{
  "text":"解約APIは POST /subscriptions/{id}/cancel（非同期・冪等）",
  "kind":"fact","scope":"project","boundary_class":"internal",
  "provenance":{"git":{"commit":"abc123","repo":"org/repo"}},
  "content_hash":"sha256:1d..."
}'
```

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_upsert \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d '{
  "text":"Stripe webhook は 10 分の時刻ドリフトを許容",
  "kind":"fact","scope":"project","boundary_class":"internal",
  "provenance":{"git":{"commit":"def456","repo":"org/repo"}},
  "content_hash":"sha256:2e..."
}'
```

### activate（AC を構成し、前提をまとめて取得）

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_activate \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d '{"q":"解約/返金 仕様","scope":["project"],"allow":["answer:task"],"top_k":12}'
```

### boundary.validate（生成前の境界チェック＆マスク）

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_boundary_validate \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d '{"payload":"連絡は ryo@example.com へ","allow":["answer:task"],"scope":"project"}'
```

### feedback（採用/棄却を学習）

```bash
curl -s -X POST http://localhost:8787/tools/pce_memory_feedback \
 -H "Authorization: Bearer $PCE_TOKEN" -H 'Content-Type: application/json' \
 -d '{"claim_id":"clm_7k","signal":"helpful","score":1.0}'
```

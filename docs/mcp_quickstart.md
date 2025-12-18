# MCP Quickstart — pce-memory を 5 分で動かす

> **ゴール**：IDE/コードエージェント（Cursor / Codex / Claude Code 等）から **MCP** 経由で pce-memory を呼び、  
> `activate → boundary.validate → upsert → feedback` の **E2E** を一度まわす。
>
> **デフォルト**：常駐サーバ不要の **stdio** トランスポート（必要時に子プロセス起動）。HTTP/WS は付録を参照。

## 最短：npx 一発セットアップ（30 秒）

> まずは“動く環境”を最速で作るための 2 ルート。
>
> - **A. 公開パッケージが利用可能な場合**（推奨）
> - **B. いますぐ試すローカル雛形（degit）**

### A) npx で初期化（公開パッケージ想定）

```bash
# 例: 公式スキャフォルダ（公開済みの場合）
npx @caphtech/create-pce-memory@latest my-pce-memory
cd my-pce-memory
pnpm i && pnpm dev   # または npm/yarn
```

- これで `policy/base.yaml` と MCP 設定、`pce-memory server` の起動スクリプトが生成されます。
- パッケージが未公開の場合は **B)** を利用してください。

### B) npx degit で雛形を取得（GitHub テンプレート）

```bash
# 例: GitHub テンプレート（任意のテンプレURLに置き換え）
# degit はリポジトリのサブディレクトリも取得できます
npx -y degit <your-org>/<your-repo>/<template-path> pce-memory-starter
cd pce-memory-starter
pnpm i && pnpm dev   # または npm/yarn
```

> ヒント: テンプレ側に `policy/base.yaml` と `mcp.config.json`（または manifest）を置いておくと、  
> `docs/mcp_quickstart.md` のステップ 1〜3 が即座に実行可能になります。

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
> npx -y @caphtech/pce-memory mcp-stdio
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
      "args": ["-y", "@caphtech/pce-memory", "mcp-stdio"],
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

- それぞれの MCP 設定で **stdio** サーバを登録（上記と同等のコマンド/引数/環境変数）
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
5. **AC の TTL を意識**：`expires_at` を超えたら再 `activate`。`policy_version` が変わったら再構成。

---

## 5. よくあるエラーと対処

| 症状              | 典型エラー              | 対処                                                     |
| ----------------- | ----------------------- | -------------------------------------------------------- |
| AC が取得できない | `POLICY_MISSING` (424)  | `policy.apply` を先に実行                                |
| 想起が拒否される  | `BOUNDARY_DENIED` (403) | `scope/allow` を見直す・`boundary.validate` で redaction |
| upsert が重複     | `DUPLICATE` (409)       | 同じ `content_hash`。ID を再利用するか `text` を正規化   |
| レート制限        | `RATE_LIMIT` (429)      | `Retry-After` 秒後に指数バックオフ＋ジッタ再試行         |

---

## 6. 片付け（任意）

- 作業 AC を失効させる：`expires_at` 待ち、または実装依存の `ac.invalidate` があれば呼ぶ。
- 監査ログを確認：`request_id/trace_id/policy_version` で関連呼び出しを相関。

---

## 付録 A：MCP Manifest（参考）

```json
{
  "name": "pce-memory",
  "version": "0.1.0",
  "tools": [
    { "name": "pce_memory_activate" },
    { "name": "pce_memory_search" },
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

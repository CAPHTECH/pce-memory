# Boundary & Policy Reference (pce-memory)

> **目的**  
> pce-memory における **境界（Boundary）** と **ポリシー（Policy）** の設計・適用・監査の基準を定義する。  
> LCP/AC（二相）の運用、Pace Layering（速・中・遅）、MCP ツール、Redact-before-Send を含む。

---

## 0. 用語と原則

- **境界（Boundary; B）**：用途・機密・不変量で _許可/編集/拒否_ を決める閾。
- **不変量（Invariants; I(B)）**：関係が変動しても保持すべき制約（例：破壊的変更禁止）。
- **用途タグ（allow）**：`answer:task`, `tool:*`, `tool:contact-lookup` 等。
- **境界クラス（boundary_class）**：`public | internal | pii | secret`。
- **スコープ（scope）**：`session（速）| project（中）| principle（遅）`。
- **Redact-before-Send**：外部 API 送出前に PII/Secret をマスク。
- **Fail-closed**：境界/ポリシー未成立時は拒否で応答。
- **Provenance-by-Default**：想起・更新・適用の全過程に由来と policy_version を付帯。

---

## 1. 適用ポイント（Enforcement Points）

### 1.1 Retrieval / Activation

- `pce_memory_search` / `pce_memory_activate` は **前置フィルタ**で `scope/allow/boundary_class` を照合。
- AC 生成関数 `r(q, C^L, B, policy, critic)` は、許可範囲内の断片のみを候補にする。
- 返却は **read-only**、出典（evidences）と `policy_version` を必須。

### 1.2 Generation 前後

- 生成 **前**：`pce_memory_boundary_validate(payload, allow?, scope?)` を必ず呼ぶ。
- 生成 **後**：必要に応じて再度 `validate`、許可外の語や PII/Secret を自動 Redact。

### 1.3 Write（Upsert / Distill / Rollback）

- `pce_memory_upsert` は `boundary_class` 必須。`secret` は原則拒否（例外は人手レビュー）。
- **Distill（蒸留）**：AC→LCP 昇格時は I(B) を再検証し、由来を必須添付。
- **Rollback（沈降）**：越境/誤り検知時に LCP の安全側へ巻戻す（監査ログと連動）。

### 1.4 エスカレーション（human_review）

- **SLA**：24h 以内に許可／拒否／条件付許可（redact 強化）を決定。
- **記録**：承認者／理由／有効期限／影響範囲を provenance に格納。
- **恒久反映**：承認が常態化するケースは policy に昇格（PR／署名）。

---

## 2. ポリシー構造（YAML）

```yaml
version: 0.1
meta:
  name: base
  owner: platform-team@example.com
  updated_at: 2025-11-11T00:00:00Z
scopes:
  session: { ttl: '7d', max_tokens: 20000 }
  project: { ttl: '120d', max_tokens: 50000 }
  principle: { ttl: 'inf', max_tokens: 100000 }
boundary_classes:
  public:
    allow: ['*']
  internal:
    allow: ['answer:task', 'tool:*']
  pii:
    allow: ['tool:contact-lookup']
    redact: ['name', 'email', 'phone']
    escalation: 'human_review'
  secret:
    allow: []
    escalation: 'deny'
invariants:
  - name: no_destructive_change
    applies_to: ['principle', 'project']
    rule: 'api.breaking_change == false'
  - name: pii_not_in_prompt
    applies_to: ['session', 'project', 'principle']
    rule: 'prompt.contains_pii == false'
redact_policies:
  default:
    rules:
      - { name: email, find: "(?i)[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,}", replace: '[email]' }
      - { name: phone, find: "\\+?\\d[\\d\\-\\s]{7,}\\d", replace: '[phone]' }
      - { name: secret, find: '(?i)sk-[a-z0-9]{10,}', replace: '[secret]' }
retrieval:
  hybrid:
    alpha: 0.65 # [0.3, 0.9] 推奨レンジ
    k_txt: 48 # k_final の 3〜5倍
    k_vec: 96 # k_final の 6〜10倍（VSS は 1.5〜2.0倍）
    k_final: 12
  rerank:
    use_quality: false # true で g に quality を掛け合わせ
    recency_half_life_days: 30
    recency:
      half_life_days_by_kind:
        fact: 120
        task: 14
        preference: 90
        policy_hint: 365
```

### 2.1 版管理と互換

- `version` は SemVer。破壊変更は MAJOR 増加時のみ。
- `policy.apply` には `dry_run/validate_only/expected_version/signature/approver` を推奨。

### 2.a retrieval パラメータ（ハイブリッド/再ランク）

- `retrieval.hybrid.alpha`：テキスト（FTS/ILIKE）とベクトル（cos/VSS）の融合係数。既定 **0.65**。クエリ性質に応じた動的調整可（`activation-ranking.md` 参照）。
- `retrieval.hybrid.k_txt / k_vec / k_final`：候補集合のサイズ。既定は **k_txt=48 / k_vec=96 / k_final=12**。
- `retrieval.rerank.use_quality`：`g` に `quality` を乗算するかのフラグ（既定 false）。
- `retrieval.rerank.recency_half_life_days`：再ランク `recency` の半減期（既定 30 日）。
- `retrieval.rerank.recency.half_life_days_by_kind`：`kind` 別の半減期。`fact=120, task=14, preference=90, policy_hint=365` を初期値とする。
- **実装**：`pce_memory_activate` / `pce_memory_search` は、これらのパラメータを読み込み `r/S/g` の計算に反映する（詳細は `activation-ranking.md`）。

### 2.x 合成・優先順位（precedence）

- **deny > redact > allow**（強い順）。deny が1つでも成立すれば拒否、次に redact で満たせるなら編集、最後に allow。
- **境界クラスの優先**：`secret > pii > internal > public`（厳格な方が勝つ）。
- **スコープの優先**：`principle > project > session`（遅層が錨）。下位層は上位層を緩和しない。
- **allow のワイルドカード**：`tool:*` は前方一致のグロブ。複数一致時は**最も制限的**な解を選ぶ。
- **衝突時**：明示 deny が1つでもあれば deny、明示 allow のみであれば最も制限的な redact を適用。

### 2.y ルールDSL（最小）

- **型**：boolean / number / string / enum
- **演算**：`== != > >= < <= && || !`、括弧 `()`
- **環境変数（例）**：`api.breaking_change:boolean`、`prompt.contains_pii:boolean`、`network.egress:list`
- **評価**：未定義変数は `false` 扱い。評価失敗は deny（fail-closed）。
- **例**：`api.breaking_change == false && "prod" notin(network.egress)`

### 2.z Redact 仕様（安全策）

- **順序**：上から順に適用（先勝ち）。一致範囲が重なるときは長い方を優先。
- **国際化**：日本語氏名／住所／携帯は専用 detector を併用（regex 単独禁止）。
- **DoS 対策**：正規表現には最長 10k 文字・バックトラック上限を設ける。
- **不可解時**：redact 不可（検出不能）は deny にフォールバック（fail-closed）。

---

## 3. 検証モデル（前後条件／境界整合）

**境界整合**：任意の B と不変量 I(B) について

```
pre_B(s, C, P) ∧ I(B)  ⇒  D = f(s, C, P) ⊧ post_B(D) ∧ I(B)
```

**Hoare 風：**

- Gating：`{ s ∈ S ∧ I(B) } gate(B) { s' ∈ S' ∧ I(B) }`
- Translation：`{ (s, C) ∧ I(B) } translate(B) { (s*, C*) ∧ I(B) }`
- Mediation：`{ conflict(C) } mediate(B) { consensus(C') ∧ evidence(inscription) }`

---

## 4. テンプレート（最小セット）

### 4.1 個人開発（dev）

```yaml
version: 0.1
boundary_classes:
  public: { allow: ['*'] }
  internal: { allow: ['answer:task', 'tool:*'] }
  pii: { allow: ['tool:contact-lookup'], redact: ['email', 'phone'], escalation: 'human_review' }
  secret: { allow: [], escalation: 'deny' }
invariants:
  - { name: 'pii_not_in_prompt', applies_to: ['*'], rule: 'prompt.contains_pii == false' }
```

### 4.2 チーム（team）

```yaml
version: 0.1
scopes: { session: { ttl: '7d' }, project: { ttl: '120d' }, principle: { ttl: 'inf' } }
boundary_classes:
  public: { allow: ['*'] }
  internal: { allow: ['answer:task', 'tool:*'] }
  pii: { allow: ['tool:contact-lookup'], redact: ['email', 'phone'], escalation: 'human_review' }
  secret: { allow: [], escalation: 'deny' }
invariants:
  - {
      name: 'no_destructive_change',
      applies_to: ['project', 'principle'],
      rule: 'api.breaking_change == false',
    }
  - { name: 'pii_not_in_prompt', applies_to: ['*'], rule: 'prompt.contains_pii == false' }
```

### 4.3 組織（org）

```yaml
version: 1.0
meta: { owner: 'sec-gov@example.com' }
scopes: { session: { ttl: '7d' }, project: { ttl: '180d' }, principle: { ttl: 'inf' } }
boundary_classes:
  public: { allow: ['*'] }
  internal: { allow: ['answer:task', 'tool:*'] }
  pii:
    {
      allow: ['tool:contact-lookup'],
      redact: ['email', 'phone', 'address'],
      escalation: 'human_review',
    }
  secret: { allow: [], escalation: 'deny' }
invariants:
  - {
      name: 'prod_data_masked',
      applies_to: ['*'],
      rule: "dataset.origin != 'prod' || data.masked == true",
    }
  - {
      name: 'no_destructive_change',
      applies_to: ['project', 'principle'],
      rule: 'api.breaking_change == false',
    }
  - {
      name: 'ip_whitelist_only',
      applies_to: ['session', 'project'],
      rule: 'network.egress in allowlist',
    }
redact_policies:
  default:
    rules:
      - { name: email, find: "(?i)[A-Z0-9._%+-]+@[A-Z0-9.-]+\\.[A-Z]{2,}", replace: '[email]' }
      - { name: secret, find: '(?i)sk-[a-z0-9]{10,}', replace: '[secret]' }
```

---

## 5. MCP ツールと境界

- **validate**：`pce_memory_boundary_validate(payload, allow?, scope?)`
  - `allowed: boolean`, `redacted?: string`, `reason`, `policy_version`
- **activate/search**：`scope/allow` を必須化。候補は境界内の断片のみ。
  - `retrieval.*` パラメータ（hybrid/rerank）は `activate`/`search` 内のスコアリングに適用される（`activation-ranking.md` 参照）。
- **upsert**：`boundary_class` 必須、`secret` は原則拒否、`pii` は redact 済みを要求。
- **policy.apply**：`dry_run/validate_only/expected_version` で競合回避（GitOps 推奨）。

### 5.x LCP/AC の寿命と再利用

- **AC**：`expires_at` 超過で無効（410）。同一 `q/policy_version` でも actor が異なれば再生成。
- **LCP**：`ttl` は scope に従う。沈降（rollback）時は snapshot を残す（append-only）。

---

## 6. Pace Layering と昇格/沈降

| 層    | 例         | 更新テンポ     | 役割               |
| ----- | ---------- | -------------- | ------------------ |
| micro | 会話・注意 | 速（秒〜日）   | 実験・発見・変異   |
| meso  | 手続・規約 | 中（週〜月）   | 蒸留・標準化・普及 |
| macro | 制度・規範 | 遅（年〜十年） | 保全・安全・責任   |

- **昇格（distill）**：AC 成果 → レビュー 2 名・由来必須・I(B) 満足 → LCP へ。
- **沈降（rollback）**：越境や事故時に LCP を安全側へ戻す（append-only ログと連動）。

---

## 7. 運用（ガバナンスと監査）

- **変更管理**：`policy.apply` は PR（reviewers ≥ 2）→ 署名 → 反映。
- **監査ログ**：append-only / WORM 推奨。`request_id/trace_id/policy_version` を常時記録。
- **SLO（例）**：Boundary 準拠率 ≥ 99.9%、Rollback MTTR ≤ 24h、蒸留半減期 30 日以内。

### 7.x 監査ログ（必須項目）

- `ts, request_id, trace_id, actor, tool, scope, boundary_class, policy_version`
- `decision {allowed|redacted|denied}`, `reason`, `redacted_count`, `hashes_of_PII`
- 保持：90日（dev）／365日（org）。PII は不可逆ハッシュで要約保存。

---

## 8. テスト（チェックリスト）

### 8.x 境界テスト・ベクトル（例）

- 入力：`payload="連絡は x@example.com まで", scope=project, class=pii`
  - 期待：`allowed=true, redacted="連絡は [email] まで"`
- 入力：`payload="APIに破壊的変更", scope=principle, invariant=no_destructive_change`
  - 期待：`allowed=false, reason="I(B) violation"`

- [ ] `validate` が `allowed=false` を返す境界違反ケース
- [ ] Redact 正規表現で PII/Secret を確実に置換
- [ ] `upsert` の `pii/secret` 入力の拒否/例外経路
- [ ] Distill/rollback の人手レビュー/ログ一貫性
- [ ] `activate/search` の allow/scope での絞り込み
- [ ] 期限切れ AC（410 Gone）の挙動

---

## 9. 付録：Policy YAML 検証用 JSON Schema（抜粋）

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "version": { "type": "string", "pattern": "^\\d+\\.\\d+\\.\\d+.*$" },
    "scopes": { "type": "object" },
    "boundary_classes": { "type": "object" },
    "invariants": { "type": "array", "items": { "type": "object" } },
    "redact_policies": { "type": "object" }
  },
  "required": ["version", "boundary_classes"]
}
```

### 9.x 検証スキーマ（拡張）

```json
{
  "type": "object",
  "additionalProperties": false,
  "properties": {
    "version": { "type": "string", "pattern": "^\\d+\\.\\d+\\.\\d+.*$" },
    "scopes": {
      "type": "object",
      "additionalProperties": false,
      "properties": {
        "session": { "type": "object", "properties": { "ttl": { "type": "string" } } },
        "project": { "type": "object", "properties": { "ttl": { "type": "string" } } },
        "principle": { "type": "object", "properties": { "ttl": { "type": "string" } } }
      }
    },
    "boundary_classes": { "type": "object", "additionalProperties": false },
    "invariants": {
      "type": "array",
      "items": {
        "type": "object",
        "additionalProperties": false,
        "properties": {
          "name": { "type": "string" },
          "applies_to": { "type": "array", "items": { "type": "string" } },
          "rule": { "type": "string" }
        },
        "required": ["name", "rule"]
      }
    },
    "redact_policies": { "type": "object" },
    "retrieval": {
      "type": "object",
      "additionalProperties": false,
      "properties": {
        "hybrid": {
          "type": "object",
          "additionalProperties": false,
          "properties": {
            "alpha": { "type": "number", "minimum": 0.0, "maximum": 1.0 },
            "k_txt": { "type": "integer", "minimum": 1 },
            "k_vec": { "type": "integer", "minimum": 1 },
            "k_final": { "type": "integer", "minimum": 1 }
          },
          "required": ["alpha", "k_txt", "k_vec", "k_final"]
        },
        "rerank": {
          "type": "object",
          "additionalProperties": false,
          "properties": {
            "use_quality": { "type": "boolean" },
            "recency_half_life_days": { "type": "number", "minimum": 1 },
            "recency": {
              "type": "object",
              "additionalProperties": false,
              "properties": {
                "half_life_days_by_lind": {
                  "type": "object",
                  "additionalProperties": { "type": "number", "minimum": 1 }
                }
              }
            }
          }
        }
      }
    }
  },
  "required": ["version", "boundary_classes"]
}
```

---

## 10. 参考

- PCE: Boundary / Invariants / Distill / Rollback（pce.ja.md, pce-model.ja.md）
- MCP Tools: `boundary.validate`, `policy.apply`, `search/activate`, `upsert`（mcp-tools.md）
- Trust & Safety: Redact-before-Send / Fail-closed（pce-memory-vision.ja.md）

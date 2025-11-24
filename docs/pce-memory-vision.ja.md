# pce-memory ビジョン

> **一行宣言**  
> 人とエージェントが **境界（Boundary）** のもとで **文脈（Context）** を共有し、**記述化（Inscription）** と **批評（Critic）** を通じて学び続けるための、**自己ホスト可能なプロセス記憶基盤**。

---

## なぜ今か（Why Now）

1. **ステートレスAIの限界** ― LLM は毎回ゼロから推論し、継続的な文脈・約束・由来を保持できない。  
2. **文脈漂流と漏洩リスク** ― コンテキストが拡張されるほど、**用途外利用**・**機密逸脱** が起こりやすい。  
3. **速度差（Pace Layering）の断絶** ― セッション（速）・チーム手続（中）・制度（遅）の更新テンポが噛み合わず、**知識が定着しない／凍結する**。

**pce-memory** は、PCE（Process‑Context Engine）の理念に基づき、  

- **潜在的コンテキストプール（LCP; Latent Context Pool）** と  
- **アクティブコンテキスト（AC; Active Context）**、  
- **境界（Boundary）と不変量（Invariants）**、  
- **記述化（Inscription）と由来（Provenance）**、  
- **批評（Critic）と成功条件束（Success Bundle）**  
を中核に据え、**「安全に覚え、速く忘れ、必要に応じて正しく想起する」** を実装する。

---

## ミッション（Mission）

> **プロセスと文脈の往還を可視化し、再現可能な学習ループをあらゆる開発・運用現場に埋め込む。**

---

## ビジョン（Vision）

- **自己主権的な記憶**：SaaS 依存に偏らず、**ローカル／オンプレ**で **境界ファースト**に運用できる。  
- **関係としての記憶**：意味は固定物ではなく **関数**。LCP↔AC の往還、翻訳・媒介・記述化で育つ。  
- **速度に整合する記憶**：セッション（速）→手続（中）→制度（遅）へ **蒸留（distill）**。事故時は **沈降（rollback）**。  
- **可撤・可視の記憶**：常に由来が辿れ、**いつでも取り消せる**。誤りは資産化され、学習へ回収される。  
- **共存の記憶**：人・エージェント・制度が **同じ境界** のもとで協働し、**危険は前段で止まり、有用は後段へ昇格**する。

---

## 原則（Tenets）

1. **Boundary‑First**：用途・機密・由来で **許可／編集／拒否** を先に決める。  
2. **Provenance‑by‑Default**：すべての想起は根拠と経路を伴う。  
3. **LCP / AC の二相**：潜在（長期）と作動（短期）を分け、**選択→解釈→評価→蒸留** を回す。  
4. **Pace‑Aware**：更新テンポ（速・中・遅）に合わせ、**昇格／沈降**の手続きを設ける。  
5. **Critic‑in‑the‑Loop**：明示的／暗黙的フィードバックで **有用性・信頼度・再現性** を継続更新。  
6. **Interoperable**：CLI／HTTP／MCP で IDE やエージェントと接続。  
7. **Self‑Hostable & Portable**：DuckDB→Postgres/pgvector へ **可搬**。埋め込みは **OpenAI＋ローカル**の切替。  
8. **Minimal Capture**：**最小限を覚え、過剰を覚えない**。Observation→Claim→Graph の段階化。  
9. **Explainable Retrieval**：ハイブリッド検索（Dense＋BM25）＋再ランク（品質・信頼・新しさ）。  
10. **Ethics & Safety**：PII/Secret は境界で遮断、**Redact‑before‑Send** を徹底。

---

## 私たちが解決する課題（Problems → Outcomes）

| 課題 | 具体 | pce-memory の解 | 到達アウトカム |
|---|---|---|---|
| 文脈の連続性欠如 | タスク再開時に前提を喪失 | LCP→AC の選択 `r(q,C^L,B,policy)` | 再立ち上がり時間の短縮 |
| 漏洩・用途外利用 | PII/秘情報が想起に混入 | Boundary 前置フィルタ＋Redact | 不正想起の実質ゼロ化 |
| 知の凍結/漂流 | 変化が定着しない／硬直 | Pace‑aware 蒸留/沈降 | 手続の健全な進化 |
| 再現性の欠如 | 「なぜその解」に答えられない | Provenance＋Inscription | 監査可能な意思決定 |
| フィードバック不全 | 学びが蓄積しない | Critic＋成功条件束 | 継続的改善の定常化 |

---

## 製品ピラー（Product Pillars）

1. **Memory Core（LCP/AC）**  
   - Observation→Claim→Graph。LCP に **由来付き**で蓄積、AC はクエリ適応で選択・要約。  
2. **Boundary Engine**  
   - 不変量・前後条件・用途タグ。**Gate / Translate / Mediate** を定義。  
3. **Retrieval & Activation**  
   - Hybrid 検索＋再ランク。**`r(q,C^L,B,policy)`** で AC を構成。  
4. **Critic & Telemetry**  
   - helpful/harmful/outdated/duplicate＋採用ログで **utility/confidence/recency** を更新。  
5. **Inscription & Governance**  
   - 監査ログ・版管理・差分。**蒸留（distill）／沈降（rollback）** 手続。  
6. **SDK / CLI / MCP**  
   - Codex／Claude Code／Cursor から **search / upsert / feedback** を叩ける統一 I/F。

---

## MCP-first（MVP）：エージェントへの機能提供

> 最初の配布形態は **MCP（Model Context Protocol）** を介した **エージェント向けツール提供**。IDE/コード・アシスタント（Codex / Claude Code / Cursor 等）から即座に使えることを最優先する。

### 提供ツール（最小）

| Tool 名 | 入力（req） | 出力（resp） | 目的 |
|---|---|---|---|
| `pce.memory.search` | `{ query, top_k?, scope?, allow? }` | `[{ claim, scores, evidences, policy_version }]` | 既知の前提・規約・禁止事項を想起 |
| `pce.memory.activate` | `{ q, scope?, allow? }` | `{ active_context_id, claims[] }` | LCP から AC を構成（r 関数） |
| `pce.memory.upsert` | `{ text, kind?, scope?, boundary_class?, entities?, relations?, provenance? }` | `{ id }` | 重要断片の登録（Observation/Claim/Graph） |
| `pce.memory.feedback` | `{ claim_id, signal: helpful|harmful|outdated|duplicate, score? }` | `{ ok: true }` | Critic による評価ループ |
| `pce.memory.boundary.validate` | `{ payload, allow?, scope? }` | `{ allowed, reason, redacted? }` | 生成前の境界チェック／Redact-before-Send |
| `pce.memory.policy.apply` | `{ yaml }` | `{ version }` | ポリシー適用（不変量・用途タグ） |

> すべてのツールは **Provenance** と **policy_version** をレスポンスに含め、監査可能性を担保する。

### 代表フロー（エージェント側）

1. **Activation**：`pce.memory.activate` で AC を取得し、プロンプト先頭に貼る（前提注入）。
2. **Generation**：候補案を生成する前に `pce.memory.boundary.validate` でチェック（必要なら redact）。
3. **Upsert**：決定事項や設計の根拠を `pce.memory.upsert` で保存。由来（commit/URL）を必須に。
4. **Feedback**：採用/棄却結果を `pce.memory.feedback` で返し、次回の再ランクに反映。

### AC 生成関数 r の骨子（擬似）

> AC = r(q, C^L, B, policy, critic)

1) **Boundary 前置**：`scope/allow/invariants` で LCP を絞る  
2) **検索**：`S = α * dense + β * BM25`（hybrid）  
3) **再ランク**：`S' = S * g(utility, confidence, recency)`（critic 反映）  
4) **Redact**：境界に従い機密を遮断（Provenance を付帯）  
5) **構成**：上位 k を AC として返す（`active_context_id` を発行）

### 安全設計

- **Boundary-First**：`validate` を生成前後に必ず呼ぶ。想起時も `scope/allow` で前置フィルタ。
- **Redact-before-Send**：MCP ツール内で PII/Secret を自動マスク。送信ログは Provenance に付帯。
- **Fail-closed**：ポリシー未読込時は許可せず、理由と対処（policy.apply）を返す。

### MCP ツールの品質特性（Mini‑Spec）

| Tool | Idempotency | Timeout | Payload | Errors(例) | Notes |
|---|---|---:|---:|---|---|
| search | safe (GET‑like) | 10s | 32KB | BOUNDARY_DENIED / RATE_LIMIT | 出典付き read‑only |
| activate | safe | 15s | 16KB | POLICY_MISSING / INVALID_SCOPE | AC の ID と構成一覧 |
| upsert | idempotent via `content_hash` | 10s | 64KB | DUPLICATE / INVALID_BOUNDARY | 由来必須（commit/URL） |
| feedback | idempotent via `(claim_id, ts bucket)` | 3s | 4KB | UNKNOWN_CLAIM | critic へ集計 |
| boundary.validate | safe | 5s | 32KB | BOUNDARY_DENIED | redact 結果を返す |
| policy.apply | non‑idempotent (versioned) | 10s | 128KB | UNAUTHORIZED | GitOps 承認を推奨 |

### MVP の対象

- IDE：**Cursor / VS Code**（拡張）
- エージェント：**Codex / Claude Code**（MCP 経由の search / upsert / feedback を標準化）

> 将来：HTTP/CLI は MCP 実装のラッパとして提供。まずは MCP を中核 I/F とすることで、エージェント統合の摩擦を最小化する。

---

## 定義と品質特性（Definitions & Qualities）

- **Critic**：採用/棄却/訂正シグナルを取り込み，`utility/confidence/recency` を更新する評価器（事前ガード／事後評価の二相）。
- **Success Bundle**：{ 整合性, 可搬性, 反事実的堅牢性, 行為的成功, 可撤性, 追跡可能性, 再現性 } の指標束。
- **Distill（蒸留）**：AC の成果を LCP に昇格する手続（重複統合・由来添付・境界整合を必須化）。
- **Rollback（沈降）**：誤りや越境が判明した場合に LCP を安全側へ巻戻す手続（影響範囲・由来を明示）。
- **Invariants**：境界の核となる不変量。違反時は fail‑closed，例外は人手レビューでのみ付与。

---

## ステークホルダー価値

- **個人開発者**：タスク再開が速い。IDE エージェントが**先に前提を読む**。  
- **チーム**：決定理由が残り、**事故の再発防止知識**が自動で昇格。  
- **組織**：規範・制度（遅層）に準拠した**安全なAI活用**が可能。  
- **研究者**：由来と版で**追試可能性**が上がる。

---

## 成功条件束（North Star & KPIs）

- **Boundary 準拠率**（許可外想起の発生率 ≈ 0）  
- **Provenance 充足率**（回答に付随する由来リンク率）  
- **TTR（Time‑to‑Retrieval）**（有用想起までの所要時間）  
- **蒸留半減期**（AC→LCP 昇格までの平均サイクル）  
- **Rollback MTTR**（誤り検知から巻戻しまでの時間）  
- **Critic 収束度**（utility/confidence の安定性）

### KPI の測定式（例）

- **Boundary 準拠率（14日移動窓）**  
  = 1 − ( 許可外想起数 / 総想起数 )
- **Provenance 充足率（14日）**  
  = 出力に有効な由来リンクを持つ応答数 / 総応答数
- **TTR p90（14日）**  
  = 1件の有用想起（feedback=helpful）までの時間の90%点
- **蒸留半減期（30日）**  
  = AC から LCP 昇格までの中央値（days）
- **Rollback MTTR（30日）**  
  = 「誤り検知」から「LCP修復」までの平均時間
- **Critic 収束度（30日）**  
  = Var(utility) の週次変化率（↓安定化が良）

---

## ロードマップ（Themes）

- **v0.1**：単ノード Core（DuckDB）、LCP/AC、Boundary 基本、CLI/MCP  
- **v0.2**：Graph メモリ、Re‑rank、Critic/Telemetry、Provenance 強化  
- **v0.3**：Pace‑aware 蒸留/沈降、Boundary UI、監査ビュー  
- **v0.4**：Postgres/pgvector、組織運用、テンプレポリシー、コネクタ  
- **v1.0**：運用実績基盤化（SLO/SLA）、監査証跡、エコシステム公開

---

## 非目標（Non‑Goals）

- 中央集権的 SaaS への固定化  
- エージェント・オーケストレータとしての全面代替  
- 収集のための収集（**過剰キャプチャ**）  
- 由来のないブラックボックス記憶

---

## 倫理・安全（Trust & Safety）

- **Redact‑before‑Send**、**最小権限**、**データ最小化**  
- PII/Secret は `boundary_class` で遮断、**人手レビューのエスカレーション**  
- 透明性：**由来・境界・方針** を常時提示

## Threat Model（最小）

| 脅威 | 説明 | 対策 |
|---|---|---|
| 越境想起 | 境界外の断片がACに混入 | boundary.validate の前置 / allowlist / fail‑closed |
| Prompt Injection | 想起断片が生成系を汚染 | 出典必須・危険トークン遮断・sandbox提示 |
| PII/Secret 漏洩 | 機密が外部APIへ送出 | Redact‑before‑Send / scope別遮断 |
| 重複/矛盾 | upsertの再送・競合 | content_hash / CRDT戦略 / 人手レビュー |
| 監査の不全 | 由来やpolicy_versionの欠落 | provenance必須・append‑only ログ |

---

## 物語（シナリオ 60秒）

> 朝、IDE を開くと pce-memory が **昨日の決定**・**関連設計**・**禁止事項** を先頭に提示する。  
> 生成案は **境界** を通過し、危険は前段で遮断。採用された断片は夜間に **蒸留** され、  
> チームの規約へ **昇格**。失敗は **由来付きで巻戻し**、二度目は起こらない。

---

## 呼びかけ（Call to Action）

- **今日から**：個人プロジェクトで LCP/AC＋Boundary を有効化し、**前提→提案→蒸留** を一巡させる。  
- **今月中**：チームの**不変量**（守るべき制約）を 5つだけ言語化し、Boundary に埋め込む。  
- **今四半期**：Critic と監査ビューで **昇格／沈降** の運用を定着させる。

## 導入ランブック（30‑60‑90）

- **Day 0‑30**：Boundary 最小セット（不変量5）／MCP search+validate を IDE に接続／KPI 基線化  
- **Day 31‑60**：feedback→critic を有効化／distill の人手レビュー運用開始／Redact‑before‑Send テスト  
- **Day 61‑90**：rollback 手順の演習／pace‑aware 昇格のSLO設定／監査ビュー公開

---

### 用語（抜粋）

- **LCP**：潜在的コンテキストプール（長期の関係的記憶）  
- **AC**：アクティブコンテキスト（短期の作動集合）  
- **Boundary / Invariants**：用途・機密・不変量  
- **Inscription / Provenance**：記述化・由来  
- **Critic / Success Bundle**：批評・成功条件束

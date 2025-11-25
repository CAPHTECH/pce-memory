# Spec Overview (Alloy & TLA+)

- 目的: PCE Memory の安全性/境界ポリシーを形式検証するための Alloy/TLA+ 雛形。
- 配置: `docs/spec/alloy/` と `docs/spec/tlaplus/`。

## 対応表（コード ↔ モデル）
| 実装概念 | Alloy | TLA+ |
|---|---|---|
| Scope | `Scope` | `Scope` constant set |
| Allow tags (`allow`) | `AllowTag` | `AllowTag` |
| Boundary class | `BoundaryClass` | — (抽象化) |
| Policy version | `PolicyVersion` | `PolicyVersion` |
| Claim | `Claim` (scope, klass, hash, version, fields, provenance) | `claims[ch]` record |
| Active Context | `ActiveContext` (claims, allow, scopeFilter, policy, expires) | `acs[id]` record |
| Feedback signal | `Helpful/Harmful/Outdated` | `Feedback` (+ critic) |
| Rate limit | — | `rateState` + `RateLimit/ResetRate/RefillTick` |
| Critic score | — | `critic` map + bounds |
| Request/trace | — | `logs.req` + `reqCounter` |
| Actions (MCP tools) | run/check scenarios | `Upsert/Activate/BoundaryValidate/Feedback/ExpireAC` |

## 実装対応の目安
| 仕様変数/アクション | 実装ファイル | シンボル |
|---|---|---|
| `claims` | `apps/pce-memory/src/store/claims.ts` | `Claim`, `upsertClaim()`, `listClaimsByScope()`, `findClaimById()` |
| `acs` | `apps/pce-memory/src/store/activeContext.ts` | `ActiveContext`, `saveActiveContext()` |
| `logs` | `apps/pce-memory/src/store/logs.ts` | `AuditLog`, `appendLog()`, `recordAudit()`, `AuditFileRecord` |
| `rateState` | `apps/pce-memory/src/store/rate.ts` | `initRateState()`, `checkAndConsume()`, `setRate()`, `resetRates()` |
| `critic` | `apps/pce-memory/src/store/critic.ts` | `updateCritic()` |
| `Upsert` | `apps/pce-memory/src/index.ts` | `pce.memory.upsert` handler |
| `Activate` | `apps/pce-memory/src/index.ts` | `pce.memory.activate` handler |
| `BoundaryValidate` | `apps/pce-memory/src/index.ts` | `pce.memory.boundary.validate` handler |
| `Feedback` | `apps/pce-memory/src/index.ts` | `pce.memory.feedback` handler |
| `ApplyPolicy` | `apps/pce-memory/src/index.ts` | `pce.memory.policy.apply` handler, `applyPolicy()` |
| `RefillTick` | `apps/pce-memory/src/store/rate.ts` | 時間窓リセット: `checkAndConsume()` 内 `resetNeeded` ロジック |
| DB初期化 | `apps/pce-memory/src/db/connection.ts` | `initDb()`, `initSchema()`, `getConnection()` |
| 環境設定 | `apps/pce-memory/src/config/env.ts` | `loadEnv()`, `Env` |
| 監査フィルタ | `apps/pce-memory/src/audit/filter.ts` | `redactSensitiveFields()`, `sanitizeForAudit()`, `computeDigest()` |

## 使い方メモ
- Alloy: `boundary.als` を Alloy Analyzer で開き、`run {}` や `check noDenyLeak` を実行。
- TLA+: `tlc docs/spec/tlaplus/pce_memory.tla`（デフォは `pce_memory.cfg` = medium、軽量は `pce_memory.small.cfg`）。`TLA_CFG` 環境変数で cfg を切替可。

## 今後の TODO
- TLA+: Boundary validate fail-closed の応答コード語彙や fairness 条件を精緻化。
- Alloy: escalation/マスク対象フィールドの優先順位、scope TTL を時間軸で表現。
- 双方向: 実装の型名とモデルのラベルをさらに合わせ、生成コードとのテストハーネスを追加。

## 設計検討メモ

### RateLimitCap バケット別切り替え（P3）
**現状**: `RateLimitCap` は全バケット共通の定数（TLA+: `Cap(b) == RateLimitCap`、実装: `cap()` 関数で `PCE_RATE_CAP` 環境変数を参照）。

**拡張案**:
1. **環境変数方式**: `PCE_RATE_CAP_tool=100`, `PCE_RATE_CAP_activate=50` のようにバケット別に設定
2. **ポリシー方式**: `policy.yaml` に `rate_limits: { tool: 100, activate: 50 }` を追加
3. **TLA+対応**: `Cap(b)` を `RateLimitCapMap[b]` に変更し、バケット別定数を導入

**推奨**: 現状の共通値で運用し、必要性が明確になった時点で環境変数方式を採用。

### OpTag 拡張（P3）
**現状**: TLA+ では `OpTag` として `"upsert"`, `"activate"`, `"validate"`, `"validate.deny"`, `"feedback"`, `"rate"`, `"rate.reset"` を使用。実装の `appendLog()` でも同様の `op` フィールドを記録。

**拡張候補**:
- `"observe"`: 読み取り専用操作のログ
- `"search"`: 検索/クエリ操作
- `"policy.apply"`: ポリシー適用（既に実装済み）
- `"expire"`: AC期限切れイベント

**推奨**: 現状で十分。`observe`/`search` は必要性が出た時点で追加。

### Live/Fairness 追加（P3）
**現状**: TLA+ に `Fairness == WF_vars(RefillTick)` と `Live_ActivateEventually` を定義済み。実装の `checkAndConsume()` は時間窓リセットを実装（`PCE_RATE_WINDOW` 秒経過でカウンタリセット）。

**検討事項**:
- `WF(ActivateAny)`: Activate操作の弱公平性（現状は検証対象外）
- `SF(Feedback)`: Feedback操作の強公平性（運用上必要なら追加）
- `<> (rateState[b] < Cap)`: レート制限が永遠にブロックしないことの保証

**推奨**: 現状の `WF(RefillTick)` で基本的な活性は保証。追加の Fairness は実運用で問題が発生した場合に検討。

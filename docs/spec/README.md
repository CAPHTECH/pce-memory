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
| 仕様変数/アクション | 想定実装箇所(例) |
|---|---|
| `claims` | apps/pce-memory/src/store/claims.ts |
| `acs` | apps/pce-memory/src/store/activeContext.ts |
| `logs` | apps/pce-memory/src/store/logs.ts |
| `rateState` | apps/pce-memory/src/store/rate.ts |
| `critic` | apps/pce-memory/src/store/critic.ts |
| `Upsert/Activate/Validate/Feedback` | apps/pce-memory/src/index.ts handlers |
| `RefillTick`(fairness) | rate-limiterの周期補充（現状は固定カウンタ、時間窓未実装） |

## 使い方メモ
- Alloy: `boundary.als` を Alloy Analyzer で開き、`run {}` や `check noDenyLeak` を実行。
- TLA+: `tlc docs/spec/tlaplus/pce_memory.tla`（デフォは `pce_memory.cfg` = medium、軽量は `pce_memory.small.cfg`）。`TLA_CFG` 環境変数で cfg を切替可。

## 今後の TODO
- TLA+: Boundary validate fail-closed の応答コード語彙や fairness 条件を精緻化。
- Alloy: escalation/マスク対象フィールドの優先順位、scope TTL を時間軸で表現。
- 双方向: 実装の型名とモデルのラベルをさらに合わせ、生成コードとのテストハーネスを追加。

# Implementation Issue List

優先度: P1（高）〜 P3（低）

## P1: 型・スキーマ基盤
- [x] P1: `packages/pce-policy-schemas` の TODO解消（Policy codec / YAMLパーサ / デフォルトポリシーエクスポート）
- [x] P1: core types 定義と実装コードの同期（docs/core-types.md & schema.md を型に落とし込む）
- [x] P1: DuckDB テーブル DDL / マイグレーション整備（claims hash unique, AC, logs, rate_state, critic）

## P1: 境界・ポリシー
- [x] P1: boundary.validate 実装（allow∩scope、redact⊆allow、policy version一致、provenance必須）
- [x] P1: policy.apply 実装（署名/読み込み、fail-closed、version管理）
- [x] P1: RateLimit（共通 Cap=1）と reqCounter / ログ単調性の実装

## P1: MCP ツール（最低限 E2E）
- [x] P1: pce.memory.upsert（hash重複検出、provenance必須、log append）
- [x] P1: pce.memory.activate（scope/allowフィルタ、policy.classes整合、AC構築）
- [x] P1: pce.memory.boundary.validate（deny時もログ記録、redaction）
- [x] P1: pce.memory.feedback（critic更新 Min/Max クリップ）
- [x] P1: pce.memory.policy.apply（初期化・更新）

## P2: サーバ起動・配線
- [x] P2: `apps/pce-memory/src/index.ts` に MCP stdio サーバ初期化＆ツール登録
- [x] P2: config/env ロード（PCE_TOKEN, PCE_POLICY パスなど）

## P2: テスト・検証
- [x] P2: ユニットテスト（boundary.validate, rate-limiter, critic, codec）→ 追加済み（boundary invalid/allowed, rate limit window, feedback critic, upsert dup）
- [x] P2: 結合テスト（upsert→activate→validate→feedback ハッピーパス＆エラーケース）
- [x] P2: formal:all を CI で実行（GitHub Actions formal.yml に unit test を追加済み。ローカル実行確認済み）

## P2: 監査・ログ
- [x] P2: 監査ログ append-only 実装（request_id / trace_id / policy_version 記録）
- [x] P2: ログに機密を残さないフィルタ

## P3: トレーサビリティ・ドキュメント
- [x] P3: docs/spec/README の仕様→実装対応表を実ファイル/シンボルで更新
- [x] P3: README に Formal Verification 手順と cfg 切替 (TLA_CFG) を追記済みか確認
- [x] P3: API / エラーレスポンス例（docs/mcp-tools.md と実装の同期）

## P3: 運用・拡張余地
- [x] P3: RateLimitCap をバケット別に切り替えられる設計余地の検討（docs/spec/README.md に設計メモ記載）
- [x] P3: OpTag 拡張（docs/spec/README.md に設計メモ記載、現状で十分と判断）
- [x] P3: Live / Fairness 追加の検討（docs/spec/README.md に設計メモ記載、現状の WF(RefillTick) で十分）

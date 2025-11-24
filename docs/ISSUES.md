# Implementation Issue List

優先度: P1（高）〜 P3（低）

## P1: 型・スキーマ基盤
- [ ] P1: `packages/pce-policy-schemas` の TODO解消（Policy codec / YAMLパーサ / デフォルトポリシーエクスポート）
- [ ] P1: core types 定義と実装コードの同期（docs/core-types.md & schema.md を型に落とし込む）
- [ ] P1: DuckDB テーブル DDL / マイグレーション整備（claims hash unique, AC, logs, rate_state, critic）

## P1: 境界・ポリシー
- [ ] P1: boundary.validate 実装（allow∩scope、redact⊆allow、policy version一致、provenance必須）
- [ ] P1: policy.apply 実装（署名/読み込み、fail-closed、version管理）
- [ ] P1: RateLimit（共通 Cap=1）と reqCounter / ログ単調性の実装

## P1: MCP ツール（最低限 E2E）
- [ ] P1: pce.memory.upsert（hash重複検出、provenance必須、log append）
- [ ] P1: pce.memory.activate（scope/allowフィルタ、policy.classes整合、AC構築）
- [ ] P1: pce.memory.boundary.validate（deny時もログ記録、redaction）
- [ ] P1: pce.memory.feedback（critic更新 Min/Max クリップ）
- [ ] P1: pce.memory.policy.apply（初期化・更新）

## P2: サーバ起動・配線
- [ ] P2: `apps/pce-memory/src/index.ts` に MCP stdio サーバ初期化＆ツール登録
- [ ] P2: config/env ロード（PCE_TOKEN, PCE_POLICY パスなど）

## P2: テスト・検証
- [ ] P2: ユニットテスト（boundary.validate, rate-limiter, critic, codec）
- [ ] P2: 結合テスト（upsert→activate→validate→feedback ハッピーパス＆エラーケース）
- [ ] P2: formal:all を CI で実行（GitHub Actions formal.yml 確認）

## P2: 監査・ログ
- [ ] P2: 監査ログ append-only 実装（request_id / trace_id / policy_version 記録）
- [ ] P2: ログに機密を残さないフィルタ

## P3: トレーサビリティ・ドキュメント
- [ ] P3: docs/spec/README の仕様→実装対応表を実ファイル/シンボルで更新
- [ ] P3: README に Formal Verification 手順と cfg 切替 (TLA_CFG) を追記済みか確認
- [ ] P3: API / エラーレスポンス例（docs/mcp-tools.md と実装の同期）

## P3: 運用・拡張余地
- [ ] P3: RateLimitCap をバケット別に切り替えられる設計余地の検討（現状は共通値のまま）
- [ ] P3: OpTag 拡張（observe / search / policy.apply 等をログ・レート対象にするかの判断）
- [ ] P3: Live / Fairness 追加の検討（ActivateAny 以外の活性が必要なら WF/SF を追加）

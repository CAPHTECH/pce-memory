# MCP Error Vocabulary (実装同期版)

- 共通レスポンスエンベロープ：

  ```json
  {
    "error": { "code": "<CODE>", "message": "..." },
    "request_id": "<uuid>",
    "trace_id": "<uuid>",
    "policy_version": "<semver>"
  }
  ```

- 使用中のコード（apps/pce-memory 実装と同期）
  - `POLICY_INVALID` : policy.apply 失敗
  - `VALIDATION_ERROR` : 入力不足・型不一致など
  - `UPSERT_FAILED` : upsert 中にエラー
  - `ACTIVATE_FAILED` : activate 中にエラー
  - `BOUNDARY_ERROR` : boundary.validate 実行時の内部エラー
  - `BOUNDARY_DENIED` : allow/scope 不一致（boundary.validate の allowed=false 時に reason と併用可）
  - `FEEDBACK_FAILED` : feedback 処理中のエラー
  - `RATE_LIMIT` : レート上限超過
  - `POLICY_MISSING` : policy 未適用（将来拡張用）
  - `DUPLICATE` : content_hash 重複（将来拡張用）

> docs/mcp-tools.md と整合が取れているか随時確認し、差分が出た場合は両方を更新してください。

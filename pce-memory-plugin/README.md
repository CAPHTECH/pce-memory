# pce-memory-plugin

Claude Code plugin for persistent knowledge management with [pce-memory](https://github.com/rizumita/pce-memory) MCP server.

## Design Philosophy

AIが自律的にpce-memoryを運用する。ユーザーは手動操作不要。

- **Auto-bootstrap**: セッション開始時にstate確認・初期化・知識想起を自動実行
- **Auto-activate**: タスク検知時に関連知識を自動想起（ユーザーへの報告不要）
- **Auto-record**: 重要な設計決定を自動記録、セッション終了時にも最終チェック
- **Auto-observe**: アーキテクチャ上重要なファイル変更時に自動記録

## Installation

```bash
claude --plugin-dir ./pce-memory-plugin
```

## How It Works

### Hooks (全自動)

| Event | Behavior |
|-------|----------|
| SessionStart | state確認→policy_apply→activate を自動実行 |
| UserPromptSubmit | タスク検知→activate を自動実行 |
| Stop | 重要決定をupsertで自動記録 |
| PostToolUse(Write\|Edit) | 重要ファイル変更時にupsertで自動記録 |

### Skills (AIが内部参照)

- **pce-core**: activate/upsert/feedback のガイド
- **pce-graph**: エンティティ・リレーション管理
- **pce-sync**: push/pull/status、CRDT マージ

### Agent

- **knowledge-curator**: 重複検出、陳腐化チェック、グラフ整合性監査

## License

MIT

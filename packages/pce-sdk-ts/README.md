# @pce/sdk-ts

TypeScript client SDK for Process-Context Engine

## Overview

`@pce/sdk-ts`はPCE Memory MCPサーバーのTypeScriptクライアントライブラリです。
型安全なMCPツール呼び出しとレスポンス検証を提供します。

## Features

- **MCP Client Wrapper**: @modelcontextprotocol/sdk上の高レベルラッパー
- **Type-safe Tool Invocation**: io-tsによる型安全なツール呼び出し
- **Request/Response Validation**: リクエスト/レスポンスの実行時検証
- **Error Handling**: PCEErrorの自動マッピング

## Installation

```bash
pnpm add @pce/sdk-ts
```

## Usage

現在の `@pce/sdk-ts` は **プレースホルダー** です（APIは未実装）。

MCPクライアント（例: `@modelcontextprotocol/sdk`）からは、以下のツール引数で呼び出せます。

### `pce.memory.observe`

```json
{
  "source_type": "chat",
  "source_id": "conv_123",
  "content": "User said: I prefer dark mode",
  "boundary_class": "internal",
  "actor": "user",
  "tags": ["preference"],
  "ttl_days": 30,
  "extract": { "mode": "single_claim_v0" }
}
```

Notes:
- `effective_boundary_class` / `warnings` が返る場合があります（例: secret検知時は保存・抽出がスキップされる）。

### `pce.memory.activate`

```json
{
  "scope": ["session", "project"],
  "allow": ["answer:task"],
  "top_k": 5,
  "include_meta": true
}
```

## Supported Tools

- `pce.memory.policy.apply` - ポリシー適用
- `pce.memory.observe` - 観察の記録（短期TTL）
- `pce.memory.upsert` - Claim登録
- `pce.memory.activate` - Active Contextの構成
- `pce.memory.boundary.validate` - 境界チェック
- `pce.memory.feedback` - フィードバック送信
- `pce.memory.state` - 状態取得

## Architecture

- `src/client.ts` - PCEClient class implementation
- `src/tools.ts` - MCP tool request/response codecs
- `src/errors.ts` - Error mapping utilities
- `src/types.ts` - Type definitions from mcp-tools.md

## Documentation

- [MCP Tools](../../docs/mcp-tools.md)
- [Core Types](../../docs/core-types.md)

## License

MIT

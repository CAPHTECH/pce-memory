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

```typescript
import { createPCEClient } from '@pce/sdk-ts';
import * as TE from 'fp-ts/TaskEither';

const client = await createPCEClient({
  transport: 'stdio',
  command: 'pce-memory',
});

// Observe
const result = await client.observe({
  source: 'user_input',
  content: 'User said: I prefer dark mode',
  metadata: { session_id: 'sess_123' },
})();

// Activate
const ac = await client.activate({
  query: 'user preferences',
  scope: ['session', 'project'],
  k: 5,
})();
```

## Supported Tools

- `pce.memory.observe` - 観察の記録
- `pce.memory.activate` - Active Contextの構成
- `pce.memory.search` - 検索のみ (AC作成なし)
- `pce.memory.feedback` - フィードバック送信
- `pce.memory.status` - 統計情報取得

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

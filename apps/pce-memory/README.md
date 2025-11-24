# @pce/memory

PCE Memory - MCP Server for Process-Context Engine

## Overview

PCE Memoryは、Process-Context Engine (PCE)の公式MCPサーバー実装です。
エージェントやLLMアプリケーションに対して、文脈記憶・検索・統合機能を提供します。

## Features

- **MCP Protocol Support**: Model Context Protocol (MCP) v1.0.4対応
- **Dual-Phase Memory**: LCP (長期) + AC (短期) の二相メモリー
- **Boundary-First Security**: スコープベースの境界管理とRedact-before-send
- **Hybrid Search**: FTS + VSS ハイブリッド検索
- **DuckDB Storage**: 組み込みDuckDBによる高速なローカルストレージ

## Installation

```bash
pnpm install
pnpm build
```

## Usage

```bash
# MCP server として起動 (stdio transport)
pce-memory

# 開発モード (watch mode)
pnpm dev
```

## Architecture

```
src/
├── index.ts          # MCPサーバーエントリーポイント
├── server/           # MCP server implementation
├── core/             # Core modules (Extractor, Integrator, Retriever, Critic)
├── db/               # DuckDB adapter
└── tools/            # MCP tool handlers
```

## Related Packages

- `@pce/boundary` - Boundary validation and redaction
- `@pce/embeddings` - Embedding provider abstraction
- `@pce/policy-schemas` - Policy schemas and validation
- `@pce/sdk-ts` - TypeScript client SDK

## Documentation

- [PCE Vision](../../docs/pce-memory-vision.md)
- [Core Types](../../docs/core-types.md)
- [MCP Tools](../../docs/mcp-tools.md)
- [Boundary Policy](../../docs/boundary-policy.md)

## License

MIT

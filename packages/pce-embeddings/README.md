# @pce/embeddings

Embedding provider abstraction for Process-Context Engine

## Overview

`@pce/embeddings`はPCEの埋め込みプロバイダー抽象化ライブラリです。
ローカル/リモート埋め込みの統一インターフェースを提供します。

## Features

- **Provider Abstraction**: 統一されたEmbeddingProviderインターフェース
- **Local Embeddings**: BAAI/bge-small-en-v1.5 (ONNX Runtime)
- **Remote Embeddings**: OpenAI, Anthropic対応
- **Batch Processing**: 効率的なバッチ埋め込み
- **Caching**: 埋め込み結果のキャッシング

## Installation

```bash
pnpm add @pce/embeddings
```

## Usage

```typescript
import { createLocalEmbeddingProvider } from '@pce/embeddings';
import * as TE from 'fp-ts/TaskEither';

const provider = createLocalEmbeddingProvider({
  modelPath: './models/bge-small-en-v1.5',
});

const result = await provider.embed(['Hello, world!'])();
```

## Supported Models

### Local (ONNX)

- BAAI/bge-small-en-v1.5 (384 dims, recommended)

### Remote

- OpenAI: text-embedding-3-small, text-embedding-3-large
- Anthropic: (TBD)

## Architecture

- `src/provider.ts` - EmbeddingProvider interface
- `src/local.ts` - Local ONNX provider
- `src/remote.ts` - Remote API provider
- `src/cache.ts` - Caching layer

## Documentation

- [Core Types](../../docs/core-types.md)

## License

MIT

# @pce/boundary

Security boundaries, policies, and redaction for Process-Context Engine

## Overview

`@pce/boundary`はPCEのBoundary-first原則を実装するライブラリです。
スコープベースのアクセス制御、機密情報のRedact、不変条件の検証機能を提供します。

## Features

- **Boundary Validation**: スコープと境界クラスによるアクセス制御
- **Redact-before-send/embed**: 送信/埋め込み前の機密情報除去
- **Invariant Evaluation**: YAML定義に基づく不変条件の実行時評価
- **Policy Enforcement**: ポリシーバージョンによる一貫性保証

## Installation

```bash
pnpm add @pce/boundary
```

## Usage

```typescript
import { validateBoundary, redactSensitive } from '@pce/boundary';
import * as E from 'fp-ts/Either';

// Boundary validation
const boundary = { scope: 'project', boundary_classes: new Set(['public', 'internal']) };
const result = validateBoundary(claim, boundary);

// Redaction
const redacted = redactSensitive(text, ['email', 'ssn', 'api_key']);
```

## Architecture

- `src/validator.ts` - Boundary validation logic
- `src/redact.ts` - Redaction functions
- `src/invariant.ts` - Invariant evaluator implementation
- `src/types.ts` - Type definitions from core-types.md

## Documentation

- [Boundary Policy](../../docs/boundary-policy.md)
- [Core Types](../../docs/core-types.md)

## License

MIT

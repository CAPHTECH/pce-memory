# @pce/policy-schemas

YAML policy schemas and validation for Process-Context Engine

## Overview

`@pce/policy-schemas`はPCEのポリシー定義とバリデーションを提供します。
YAML形式のポリシーをio-tsで検証し、型安全なポリシーオブジェクトを生成します。

## Features

- **YAML Schema Definitions**: 境界・検索・クリティックポリシーのスキーマ定義
- **io-ts Validation**: 実行時型検証とエラーレポート
- **Default Policies**: プリセットのデフォルトポリシー
- **SemVer Version Management**: ポリシーバージョンのセマンティックバージョニング

## Installation

```bash
pnpm add @pce/policy-schemas
```

## Usage

```typescript
import { parsePolicy, defaultBoundaryPolicy } from '@pce/policy-schemas';
import * as E from 'fp-ts/Either';

// Parse YAML policy
const yamlContent = '...';
const result = parsePolicy(yamlContent);

if (E.isRight(result)) {
  console.log('Policy version:', result.right.version);
}

// Use default policy
const policy = defaultBoundaryPolicy();
```

## Policy Structure

```yaml
version: '0.1.0'
boundary:
  default_scope: project
  allowed_classes: [public, internal]
  invariants:
    - name: no_destructive_changes
      applies_to: [principle]
      rule: 'forbid DELETE/DROP/TRUNCATE in principle scope'
retrieval:
  hybrid:
    alpha: 0.65
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
```

## Architecture

- `src/parser.ts` - YAML parser with io-ts validation
- `src/schemas.ts` - Policy codec definitions
- `src/defaults.ts` - Default policy templates
- `src/types.ts` - Type definitions from core-types.md

## Documentation

- [Boundary Policy](../../docs/boundary-policy.md)
- [Activation Ranking](../../docs/activation-ranking.md)
- [Core Types](../../docs/core-types.md)

## License

MIT

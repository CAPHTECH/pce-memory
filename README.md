# PCE Memory

**Process-Context Engine (PCE)** - MCP Server for Context-Aware Memory & Retrieval

[![CI](https://github.com/CAPHTECH/pce-memory/actions/workflows/ci.yml/badge.svg)](https://github.com/CAPHTECH/pce-memory/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Overview

PCE Memoryは、LLMエージェントやアプリケーションに**文脈記憶・検索・統合**機能を提供するMCPサーバーです。

### Key Features

- 🔒 **Boundary-first Security**: スコープベースの境界管理とRedact-before-send
- 🧠 **Dual-phase Memory**: LCP (長期記憶) + AC (短期記憶) の二相アーキテクチャ
- 🔍 **Hybrid Search**: FTS + VSS のハイブリッド検索 (r, S, g 関数)
- 📊 **DuckDB Storage**: 組み込みDuckDBによる高速ローカルストレージ
- 🎯 **MCP Protocol**: Model Context Protocol v1.0.4 準拠
- 🛡️ **Law-Driven Engineering**: fp-ts/io-ts によるType-safe & Property-based Testing

## Project Structure

```
pce-memory/
├── apps/
│   └── pce-memory/          # MCP server implementation
├── packages/
│   ├── pce-boundary/        # Boundary validation & redaction
│   ├── pce-embeddings/      # Embedding provider abstraction
│   ├── pce-policy-schemas/  # YAML policy schemas
│   └── pce-sdk-ts/          # TypeScript client SDK
├── docs/                    # Documentation
│   ├── pce-memory-vision.md
│   ├── core-types.md
│   ├── mcp-tools.md
│   ├── boundary-policy.md
│   └── activation-ranking.md
└── tools/                   # Development tools (TBD)
```

## Quick Start

### Prerequisites

- **Node.js**: ≥ 22.18.0 (LTS)
- **pnpm**: ≥ 9.0.0

### Installation

```bash
# Install dependencies
pnpm install

# Build all packages
pnpm build

# Run tests
pnpm test

# Run property-based tests
pnpm test:pbt
```

### Running the MCP Server

```bash
# Start MCP server (stdio transport)
cd apps/pce-memory
pnpm dev
```

### Development Workflow

```bash
# Watch mode (auto-reload on file changes)
pnpm dev

# Type checking
pnpm typecheck

# Linting
pnpm lint
pnpm lint:fix

# Formatting
pnpm format
pnpm format:check

# Clean build artifacts
pnpm clean
```

## MCP Tools

PCE Memoryは以下のMCPツールを提供します：

| Tool                           | Description                                     |
| ------------------------------ | ----------------------------------------------- |
| `pce_memory_policy_apply`      | ポリシー適用 (boundary/retrieval設定)           |
| `pce_memory_observe`           | 観察を記録 (Observation → Claims)               |
| `pce_memory_upsert`            | Claimを登録 (Long-term memory)                  |
| `pce_memory_activate`          | Active Contextを構成 (Query → AC)               |
| `pce_memory_boundary_validate` | 境界チェック / redact-before-send               |
| `pce_memory_feedback`          | フィードバックを送信 (helpful/harmful/outdated) |
| `pce_memory_state`             | 状態情報を取得 (state/policy_version)           |

詳細は [docs/mcp-tools.md](docs/mcp-tools.md) を参照してください。

### Observation（`pce_memory_observe`）の保持とセキュリティ（要点）

- Observation は短期TTLで保持し、期限後は `content` をスクラブ（NULL化）する運用を推奨します。
- `PCE_OBS_TTL_DAYS` / `PCE_OBS_TTL_DAYS_MAX` で TTL を調整できます。
- `PCE_OBS_MAX_BYTES` で `content` の最大バイト数を制限できます（既定 65536）。
- `PCE_OBS_STORE_MODE`（`raw|redact|digest_only`）で保存モードを調整できます（既定 `redact`）。
- secret を検知した場合は fail-safe として `content` を保存せず、抽出もスキップします（詳細は `docs/mcp-tools.md` の observe を参照）。

## Architecture

PCE Memoryは以下のコアモジュールで構成されます：

- **Extractor**: 観察から主張を抽出 (Observation → Claims)
- **Integrator**: 主張を統合・検証 (Claims + LCP → LCP')
- **Retriever**: 文脈を検索・活性化 (Query + LCP → AC)
- **Critic**: 主張を評価・更新 (Feedback → utility/confidence/recency)

詳細は [docs/pce-memory-vision.md](docs/pce-memory-vision.md) を参照してください。

## Testing Strategy

### Law-Driven Engineering (LDE)

PCE Memoryは**Law-Driven Engineering (LDE)**原則に従います：

1. **Type-driven Design**: fp-ts/io-ts によるBranded Types
2. **Property-based Testing**: fast-checkによる不変条件検証
3. **Errors as Values**: Either/TaskEither による明示的エラー処理
4. **Detroit School TDD**: 実際のコンポーネント連携をテスト

## Formal Verification

- `pnpm formal:tla` — TLA+ (TLC)。`tlc` が無い場合は Docker `ghcr.io/tlaplus/tlaplus` を自動利用。
- `pnpm formal:alloy` — Alloy (SAT4J)。初回実行時に jar を `.cache/formal` に取得し Java で全コマンドを走査。
- `pnpm formal:all` — 上記まとめ実行。

### Test Commands

```bash
# All tests (unit + property-based)
pnpm test

# Property-based tests only
pnpm test:pbt

# With coverage (≥ 80% required)
pnpm test --coverage

# Watch mode
pnpm test:watch
```

詳細は [packages/pce-boundary/test/README.md](packages/pce-boundary/test/README.md) を参照してください。

## Contributing

### Code Quality Gates

| Gate                  | Threshold        |
| --------------------- | ---------------- |
| Static Analysis       | 0 errors         |
| Coverage              | ≥ 80%            |
| Cyclomatic Complexity | ≤ 10             |
| Mutation Score        | ≥ 60% (optional) |

### Commit Convention

```
feat: Add new feature
fix: Fix bug
docs: Update documentation
test: Add tests
refactor: Refactor code
chore: Update build config
```

## License

MIT License - see [LICENSE](LICENSE) for details

## Documentation

- [Vision & Mission](docs/pce-memory-vision.md)
- [Core Types](docs/core-types.md)
- [MCP Tools](docs/mcp-tools.md)
- [Boundary Policy](docs/boundary-policy.md)
- [Activation Ranking](docs/activation-ranking.md)
- [DuckDB Schema](docs/schema.md)
- [Search Extensions](docs/search_extensions_duckdb.md)

## Related Projects

- [Model Context Protocol](https://modelcontextprotocol.io/)
- [fp-ts](https://gcanti.github.io/fp-ts/)
- [io-ts](https://gcanti.github.io/io-ts/)
- [fast-check](https://fast-check.dev/)
- [DuckDB](https://duckdb.org/)

## Acknowledgments

Built with ❤️ by CAPHTECH, following Law-Driven Engineering principles and inspired by:

- Ernst Cassirer's Philosophy of Symbolic Forms
- Actor-Network Theory (ANT)
- Buddhist concepts of dependent origination (縁起)

---

**Status**: 🚧 Work in Progress (MVP Phase)

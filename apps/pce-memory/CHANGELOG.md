# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.7.4] - 2025-12-13

### Added

- **MCP Prompts: sync_push / sync_pull** - Add dedicated prompts for sync operations
  - `sync_push`: Guide for exporting local knowledge to `.pce-shared/`
  - `sync_pull`: Guide for importing shared knowledge from `.pce-shared/`

### Changed

- **Translate MCP Prompts to English** - All prompt definitions and messages are now in English
  - `recall_context`, `record_decision`, `sync_workflow`, `debug_assist`
  - Improves compatibility with international users

## [0.7.3] - 2025-12-12

### Fixed

- **Fix daemon MCP prompts support** - Advertise prompts capability and implement `prompts/list` + `prompts/get` (Issue #16)
- **Stabilize CI** - Improve DuckDB retry/backoff for transient prepared statement failures

## [0.7.2] - 2025-12-12

### Fixed

- **Update MCP SDK to 1.24.3** - Improve Claude Code prompts compatibility
  - Upgrade from v1.0.4 to v1.24.3
  - Improve protocol version and capabilities support
- **Fix hardcoded SERVER_VERSION** (Issue #23)
  - Dynamically retrieve version from package.json

## [0.7.1] - 2025-12-12

### Fixed

- **Rename prompts to use underscores** - Improve Claude Code slash command compatibility
  - `recall-context` → `recall_context`
  - `record-decision` → `record_decision`
  - `sync-workflow` → `sync_workflow`
  - `debug-assist` → `debug_assist`

## [0.7.0] - 2025-12-12

### Added

- **MCP Prompts support** (Issue #16) - Provide prompt templates for common workflows
  - `recall_context`: Recall related knowledge at task start
  - `record_decision`: Assist recording design decisions
  - `sync_workflow`: Guide for Git sync workflow
  - `debug_assist`: Search related knowledge during debugging
  - Compliant with MCP Protocol Prompts specification

- **Git-based CRDT sync** (Issue #18) - Enable knowledge synchronization across teams
  - `pce.memory.sync.push` MCP tool: Export local DB to `.pce-shared/`
  - `pce.memory.sync.pull` MCP tool: Import from `.pce-shared/` (incremental sync supported)
  - `pce.memory.sync.status` MCP tool: Check sync status
  - CLI commands: `pce-memory sync push/pull/status`
  - Git hooks integration: Auto-sync via pre-commit, post-merge
  - G-Set CRDT-based conflict detection and resolution
  - boundary_class merge strategy (upgrade only)
  - dry_run mode for preview
  - TLA+/Alloy formal verification (`docs/spec/tlaplus/sync_crdt.tla`, `docs/spec/alloy/sync_conflict.als`)
  - Integration guide (`docs/git-hooks-integration.md`)

### Fixed

- Improve CI stability for hybridSearch tests
- Fix validation and error handling issues identified by Critical Review

## [0.6.0] - 2025-12-12

### Added

- **MCP Structured Output support** - Add outputSchema to all tools
  - Compliant with MCP Protocol v1.0.4 Structured Output specification
  - All handlers return both `content` (for backward compatibility) and `structuredContent` (structured data)
  - Enables type-safe response parsing
  - 16 test cases verify schema consistency

## [0.5.1] - 2025-12-12

### Fixed

- **Daemon idle timeout** - 接続ベースのアイドル判定に修正
  - アイドルタイムアウトを最終リクエスト時刻ではなく接続数で判定するよう変更
  - シャットダウン時の mutex 例外を解消
  - デフォルトタイムアウト値を定数化

## [0.5.0] - 2025-12-10

### Changed

- Migrate from `@xenova/transformers@2.17.2` to `@huggingface/transformers@3.8.1`
  - Fix sharp native binary installation error in npx environments
  - v3 uses sharp@0.34 with WASM fallback support for better cross-platform compatibility
  - API change: `quantized: true` → `dtype: 'q8'` for 8-bit quantization

## [0.4.1] - 2025-12-10

### Fixed

- Word-split OR search for text queries (#11)
  - Fix `pce.memory.activate` `q` parameter not working with multi-word queries
  - Split search query by whitespace (half-width and full-width) and match claims containing any word
  - Example: `q="state XState Valtio"` → matches claims containing "state" OR "XState" OR "Valtio"

## [0.4.0] - 2025-12-10

### Changed

- レートリミットのデフォルト値をバルク登録向けに緩和
  - `PCE_RATE_CAP`: 100 → 1000（10倍に増加）
  - `PCE_RATE_WINDOW`: 60秒 → 10秒（短縮）
  - 効果: 10秒あたり1000件、1分あたり6000件相当の操作が可能
  - 環境変数で従来値に戻すことも可能

## [0.3.7] - 2025-12-07

### Fixed

- デーモン起動時にレートリミットカウンタをリセットするよう修正
  - `initRateState()`で`INSERT OR IGNORE`から`ON CONFLICT DO UPDATE`に変更
  - 永続化DB使用時でもデーモン再起動でクリーンな状態から開始

## [0.3.6] - 2025-12-05

### Added

- Golden set evaluation with assay-kit integration (`feat(assay)`)
- `.prettierignore` configuration

### Fixed

- Add `sharp` to dependencies for npm users
- Use shared `getSocketPath` helper for adapter
- Resolve ESLint errors

## [0.3.5] - 2025-12-03

### Fixed

- Daemon shutdown hang issue
  - `server.close()` now has 5-second socket shutdown timeout
  - DuckDB connection explicitly closed via `closeDb()`
  - 10-second watchdog timer forces exit on hang
  - Fixes DuckDB lock conflict: "Could not set lock on file"

## [0.3.4] - 2025-12-01

### Fixed

- Move `workspace:*` dependencies to devDependencies
  - `@pce/*` packages are bundled by tsdown, not needed at runtime
  - Fixes "Unsupported URL Type workspace:\*" error with `npx pce-memory`

## [0.3.3] - 2025-12-01

### Fixed

- Stale startup lock detection for daemon lifecycle
  - Daemon now detects stale lock files with dead PIDs
  - Fixes "Another daemon is starting up. Exiting." error on restart

## [0.3.2] - 2025-11-28

### Fixed

- Remove `workspace:*` dependencies from published package
  - `@pce/*` packages are bundled via tsdown, not installed as npm dependencies

## [0.3.1] - 2025-11-28

### Fixed

- Local embedding (onnxruntime) now works with `npx pce-memory`
  - `@xenova/transformers` marked as external dependency (not bundled)
  - Native binary modules installed via npm at runtime

## [0.3.0] - 2025-11-28

### Added

- **Graph Memory Query Tools** (Issue #1)
  - `pce.memory.query.entity` - Query entities by ID, type, canonical_key, or claim_id
  - `pce.memory.query.relation` - Query relations by ID, src_id, dst_id, type, or evidence_claim_id
- English descriptions for all MCP tools (MCP standard compliance)

### Fixed

- CI stability improvements for DuckDB tests
  - File-based DB isolation (tmpdir + UUID)
  - Connection auto-recovery on invalid state
  - Retry wrappers for flaky tests

## [0.2.1] - 2025-11-28

### Fixed

- TypeScript `exactOptionalPropertyTypes` compliance in Graph handlers
- Added missing ErrorCode types (`UPSERT_ENTITY_FAILED`, `UPSERT_RELATION_FAILED`)
- String length validation for Entity/Relation inputs (security hardening)

### Added

- STATE_ERROR and RATE_LIMIT test cases for Graph handlers (4 new tests)

## [0.2.0] - 2025-11-28

### Added

- **Graph Memory MCP Tools** (MVP2 Priority 1)
  - `pce_memory_upsert_entity` - Register Entity (Actor/Artifact/Event/Concept)
  - `pce_memory_upsert_relation` - Register Relation between Entities
- New test suite for Graph handlers (9 tests)

## [0.1.3] - 2025-11-28

### Fixed

- Allow upsert from Ready state (Ready → HasClaims transition)
  - State machine now supports continuous claim addition after activation
  - Updated `canUpsert` to include Ready state

## [0.1.2] - 2025-11-28

### Fixed

- Remove workspace:\* dependencies from package.json (bundled via tsdown)

## [0.1.1] - 2025-11-28

### Fixed

- SERVER_NAME constants updated from `@pce/memory` to `pce-memory`

## [0.1.0] - 2025-11-28

### Added

- Initial release
- MCP Protocol v1.0.4 support
- Core MCP tools:
  - `pce_memory_policy_apply` - Policy initialization
  - `pce_memory_upsert` - Claim registration with provenance tracking
  - `pce_memory_activate` - Active context construction
  - `pce_memory_boundary_validate` - Pre-generation boundary check
  - `pce_memory_feedback` - Critic update (helpful/harmful/outdated/duplicate)
  - `pce_memory_state` - State machine status
- Pace Layering scope management (session/project/principle)
- Boundary-first security with Redact-before-send
- Hybrid search (FTS + VSS)
- DuckDB embedded storage
- Local embeddings via transformers.js
- Daemon/Client architecture for multi-client support
- BigInt timestamp serialization fix for DuckDB compatibility

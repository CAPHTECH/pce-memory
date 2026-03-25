# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.12.0] - 2026-03-25

### Added

- **Knowledge Freshness Guard**: upsert/promote returns `similar_existing` when semantically similar claims exist; activate flags stale candidates with freshness metadata
- **Usage-Based Retrieval Learning**: `retrieval_count` and `last_retrieved_at` tracking; implicit usage decay and retrieval boost in reranking — frequently retrieved claims rank higher over time without explicit feedback
- **Knowledge Maintenance Signals**: `maintenance_hints` in activate response with `similar_pairs`, `stale_candidates`, `unprocessed_observations`, and `high_retrieval_no_feedback` categories; policy-configurable
- **Claim-to-Claim Connectivity**: `claim_links` table with typed edges (`extends`, `supports`, `contradicts`, `related`); auto-suggested on promote/upsert; activate traverses 1-hop linked claims; `pce_memory_link_claims` tool
- **Working State Lifecycle**: `status` column on claims (`active`/`completed`/`stale`); auto-stale detection for working_state claims >14 days; `feedback(signal=completed)` marks tasks done; stale/completed excluded from activate by default
- **MMR Diversification**: Optional Maximal Marginal Relevance reranking to reduce result redundancy (policy-configurable)
- **Entity Graph Query Expansion**: Activate traverses entity-relation graph to expand queries beyond lexical matches
- **Feedback-Loop Scoring Boost**: helpful/harmful feedback directly impacts retrieval ranking via explicit multiplier
- **Provenance Quality Scoring**: Evidence density, provenance completeness, and promotion lineage factor into rerank scoring
- **Observation Slot Cap**: `include_observations=true` caps observation results to 30% of top_k
- **Observation Score Cap**: Raw observation recency score capped at 0.8 to prevent dominating promoted claims
- **Intent Penalty**: `policy_check` intent applies 0.1x penalty to non-norm task/working_state claims

### Changed

- **Plugin v0.4.0**: Stop hook converted from prompt to command type; hooks/skills updated for entity registration guidance
- **Competitive landscape documented**: `docs/competitive-landscape.md` with 16+ products/papers analyzed

### Removed

- **Ollama LLM entity extractor**: Removed server-side LLM extraction (4.6s latency, limited query expansion effect); entity registration is now client-side via hooks/skills guidance
- **Pattern NLP auto-extraction**: Removed automatic pattern-based entity extraction from upsert/promote (68% noise rate); `entityExtractor.ts` utility kept but not auto-called

## [0.11.0] - 2026-03-24

### Added

- **v2 Promotion Pipeline**: `pce_memory_distill`, `pce_memory_promote`, `pce_memory_rollback` tools for staged knowledge promotion with reviewable candidates, mandatory provenance, and append-only rollback
- **Intent-Aware Activate**: `intent` parameter (`resume_task`, `debug_incident`, `design_decision`, `policy_check`) with per-intent scoring adjustments
- **Type Filters**: `kind_filter` and `memory_type_filter` parameters in `pce_memory_activate` for precise retrieval
- **Observation Search**: `include_observations` parameter in `pce_memory_activate` for short-term memory recall from micro layer
- **Memory Type Taxonomy**: `memory_type` field (`evidence`, `working_state`, `knowledge`, `procedure`, `norm`) on claims as semantic axis alongside `kind`
- **Schema Primitives**: `promotion_queue`, `active_context_items` tables; enriched `active_contexts` with `intent`, `expires_at`, `policy_version`
- **Centralized Domain Types**: `ClaimKind` and `MemoryType` in `src/domain/types.ts`
- **v2 Migration Script**: `scripts/migrate-v2-memory-type.ts` for backfilling `memory_type` on existing claims
- **Policy-Driven Retrieval**: `retrieval.*` policy settings wired into runtime scoring (alpha, threshold, k_txt, k_vec)
- **Active Context Items**: Per-item score breakdown, source layer, rank, and selection reason persisted
- **Validation Framework**: Local validation workflow, task corpus, scoring rubric, and 4 architecture validation analyses
- **Design Invariant Tests**: `test/v2-design-invariants.test.ts` locking v2 architectural contracts
- **Systematic Tests**: Boundary/property-based/E2E tests across promotion, retrieval, migration, sync, and validation (+3600 lines)

### Changed

- **observe is raw-only**: `observe.extract.single_claim_v0` removed; use `distill` + `promote` for durable memory
- **Session upsert rejected**: `pce_memory_upsert` with `scope=session` returns VALIDATION_ERROR; use `pce_memory_observe`
- **Secret upsert rejected**: `pce_memory_upsert` with `boundary_class=secret` returns VALIDATION_ERROR; use `pce_memory_observe`
- **Provenance enforced**: `provenance.at` required for `project` and `principle` scope upserts
- **Boundary pre-filtering**: Boundary allow-tag filtering moved before ranking (fixes candidate budget waste)
- **Layer-aware sync**: Session claims excluded from push; rolled-back claims excluded; `memory_type` preserved in round-trip
- **Activate response enriched**: Returns `intent`, `source_layer`, `rank`, `score_breakdown`, `selection_reason` per claim

### Fixed

- Boundary filtering consumed candidate budget by running after ranking instead of before
- `upsert(secret)` was accepted despite policy rejection
- Provenance was not validated at runtime despite being documented as required
- MCP tool schemas used `oneOf`/`allOf`/`anyOf` which Claude API rejects

## [0.10.0] - 2025-12-18

### Changed

- **BREAKING: Rename all MCP tool names from dot notation to underscore notation** - Following MCP community standard (snake_case)
  - `pce.memory.policy.apply` → `pce_memory_policy_apply`
  - `pce.memory.observe` → `pce_memory_observe`
  - `pce.memory.upsert` → `pce_memory_upsert`
  - `pce.memory.activate` → `pce_memory_activate`
  - `pce.memory.boundary.validate` → `pce_memory_boundary_validate`
  - `pce.memory.feedback` → `pce_memory_feedback`
  - `pce.memory.state` → `pce_memory_state`
  - `pce.memory.upsert.entity` → `pce_memory_upsert_entity`
  - `pce.memory.upsert.relation` → `pce_memory_upsert_relation`
  - `pce.memory.query.entity` → `pce_memory_query_entity`
  - `pce.memory.query.relation` → `pce_memory_query_relation`
  - `pce.memory.sync.push` → `pce_memory_sync_push`
  - `pce.memory.sync.pull` → `pce_memory_sync_pull`
  - `pce.memory.sync.status` → `pce_memory_sync_status`
  - Clients must update tool invocations to use new names
  - See [SEP-986](https://github.com/modelcontextprotocol/modelcontextprotocol/issues/986) for MCP naming conventions

## [0.9.1] - 2025-12-18

### Fixed

- **BigInt serialization in structuredContent** - Fix MCP error when query.entity/relation returns timestamps (#38)
  - `createToolResult` now converts BigInt values in structuredContent
  - Prevents "Do not know how to serialize a BigInt" error

### Changed

- **Improved query tool descriptions** - Clarified filter requirements for `query.entity` and `query.relation`
  - Description now states "At least one filter is required"
  - Prevents LLM from calling without filters

### Added

- **BigInt serialization regression tests** - Added tests to verify structuredContent is JSON-serializable

## [0.9.0] - 2025-12-18

### Added

- **Optional content_hash in upsert** - `content_hash` parameter is now optional in `pce.memory.upsert` (#37)
  - Auto-generates SHA256 hash from text when omitted
  - Validates against provided hash when specified (existing behavior)
  - Response now includes `content_hash` field for client reference
  - Backward compatible: existing clients continue to work

## [0.8.5] - 2025-12-18

### Fixed

- **content_hash validation on upsert** - Validate that content_hash matches actual SHA256 of text during upsert (#36)
  - Prevents dummy/fake content_hash from being stored
  - Eliminates push/pull sync errors caused by hash mismatch
  - Error messages do not expose hash values for security

## [0.8.4] - 2025-12-17

### Changed

- **Improved tool parameter descriptions** - Added description to `allow` parameter in `pce.memory.activate` and `pce.memory.boundary.validate` (#35)

## [0.8.3] - 2025-12-16

### Fixed

- **WAL corruption prevention** - Execute CHECKPOINT before closing database connection to flush WAL to main DB file (#34)
  - Prevents WAL replay errors on daemon restart
  - Distinguishes error handling between `:memory:` and file-based databases
  - Adds comprehensive tests for CHECKPOINT behavior

## [0.8.2] - 2025-12-16

### Changed

- **Improved MCP tool descriptions** - Enhanced descriptions for better LLM agent tool selection (#33)
  - `pce.memory.policy.apply`: Clarified as session initialization step
  - `pce.memory.observe`: Added TTL, extraction, and PII/secret handling details
  - `pce.memory.upsert`: Differentiated from observe as permanent knowledge storage
  - `pce.memory.activate`: Explained purpose as knowledge retrieval for current task
  - `pce.memory.boundary.validate`: Clarified as pre-output security check
  - `pce.memory.feedback`: Added usage guidance for each signal type

## [0.8.1] - 2025-12-16

### Fixed

- **DuckDB FK constraint bug** - Remove foreign key constraint from `claim_vectors` table that incorrectly triggered constraint errors during `UPDATE` on parent `claims` table (#32)
- **TOCTOU race condition in critic.ts** - Replace SELECT-then-INSERT/UPDATE pattern with atomic UPSERT using `INSERT ON CONFLICT DO UPDATE RETURNING`

### Added

- **Automatic migration for existing databases** - Copy-and-swap migration with transaction protection to remove FK constraint from legacy databases
- **Orphaned temp table cleanup** - `cleanupOrphanedTempTables()` removes stale `claim_vectors_new_*` tables from interrupted migrations

## [0.8.0] - 2025-12-16

### Added

- **`pce.memory.observe` tool** (Issue #30) - Record raw observations with optional claim extraction
  - `source_type`: chat / tool / file / http / system
  - `extract.mode`: `noop` (record only) plus an early temporary legacy claim-extraction mode
  - Automatic boundary detection: PII (email/phone) → redaction, secret (API keys) → reject storage
  - GC support: `scrub` (NULL content) or `delete` (remove row) after TTL expiration
  - Evidence linking: observation → claim traceability
  - Schema migration: observations table with content_digest, expires_at, gc_mode columns

### Changed

- **State machine**: observe operation transitions state appropriately (PolicyApplied → HasClaims when claims created)

## [0.7.5] - 2025-12-13

### Changed

- **Sync: auto-detect git root for `.pce-shared/`** - Default sync directory is now resolved from the repository root when invoked from subdirectories

### Fixed

- **Sync manifest version** - `manifest.json` now records the actual `pce-memory` version (previously hardcoded)

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

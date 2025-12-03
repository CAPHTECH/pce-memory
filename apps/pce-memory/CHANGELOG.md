# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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

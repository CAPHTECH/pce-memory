# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.1.2] - 2025-11-28

### Fixed

- Remove workspace:* dependencies from package.json (bundled via tsdown)

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

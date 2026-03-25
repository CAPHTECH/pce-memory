# Auto Entity Extraction Validation Report

Generated at: 2026-03-25T04:08:46.335Z

## Assumptions

- Because the current pattern extractor does not infer abstract seed concepts like "authentication" or "caching", Tests 1 and 2 manually link those broad topic entities and treat the presence of auto-extracted sibling entities as the experimental variable.
- Test 4 compares the store-level pattern and LLM extractors directly because automatic LLM extraction is currently wired into distill, not upsert.
- All latency and retrieval measurements use a deterministic local embedding service so the experiment is repeatable without external model variance.

## Test 1: Query Expansion Improvement

Average P@3 without auto entities: 0.133

Average P@3 with auto entities: 1

Delta: 0.867

- Broad seed entities were manually linked so queries like "authentication" and "caching" had a stable graph entry point.
- The measured delta comes from the presence or absence of auto-extracted sibling entities that query expansion can traverse.

### Without Auto-Extracted Entities

| Query | P@3 | Hits | Top 3 claims |
| --- | ---: | ---: | --- |
| Authentication | 0 | 0/4 | IndexReviewBoard tracks breaking DDL before rollout. <br> apps/pce-memory/src/core/handlers.ts hosts activate validation helpers. <br> ConflictResolver compares vector clocks before commit. |
| Caching | 0 | 0/4 | FakeClockDriver advances retention windows in unit suites. <br> OAuthClient validates PKCE verifier state before token exchange. <br> JWT rotation protects access tokens during mobile sign in recovery. |
| Synchronization | 0.333 | 1/4 | SyncCursor checkpoints replica positions after batch upload. <br> apps/pce-memory/src/core/handlers.ts hosts activate validation helpers. <br> IndexReviewBoard tracks breaking DDL before rollout. |
| Schema | 0.333 | 1/4 | SchemaMigrator replays db/schema.sql during bootstrap. <br> CacheWarmer preloads hot keys during deploy cutovers. <br> OAuthClient validates PKCE verifier state before token exchange. |
| Testing | 0 | 0/4 | CACHE_TTL_SECONDS controls eviction timing for catalog pages. <br> IndexReviewBoard tracks breaking DDL before rollout. <br> RedisCache stores rendered dashboard fragments with key bucketing. |

### With Auto-Extracted Entities

| Query | P@3 | Hits | Top 3 claims |
| --- | ---: | ---: | --- |
| Authentication | 1 | 3/4 | JWT rotation protects access tokens during mobile sign in recovery. <br> AccessPolicyService records MFA checkpoint failures for sign in. <br> SessionManager closes stale refresh grants after logout. |
| Caching | 1 | 3/4 | RedisCache stores rendered dashboard fragments with key bucketing. <br> CacheWarmer preloads hot keys during deploy cutovers. <br> EdgeCachePolicy bypasses stale entries during purge storms. |
| Synchronization | 1 | 3/4 | SyncCursor checkpoints replica positions after batch upload. <br> ConflictResolver compares vector clocks before commit. <br> ReplicaScheduler defers backfill retries during congestion. |
| Schema | 1 | 3/4 | SchemaMigrator replays db/schema.sql during bootstrap. <br> IndexReviewBoard tracks breaking DDL before rollout. <br> DuckDB migration planner validates nullable columns before release. |
| Testing | 1 | 3/4 | apps/pce-memory/src/core/handlers.ts hosts activate validation helpers. <br> Vitest covers handleActivate ranking with deterministic embeddings. <br> ContractHarness snapshots MCP tool payloads for regression checks. |

## Test 2: Pattern NLP Noise

Auto-extracted entity instances: 97

Relevant instances: 31

Noise instances: 66

Unique relevant/noise entities: 15/63

Clean control P@3 for "caching": 0.667

Noisy corpus P@3 for "caching": 0

Degradation observed: true

Clean top 3: RedisCache keeps fragment payloads hot across shard moves. | EdgeCachePolicy bypasses stale fragments during rollback. | SchemaMigrator reused CACHE_PREVIEW_DAY staffing spreadsheets.

Noisy top 3: CacheStandup2026 and CACHE_REVIEW_2026 picked lunch options for visitors. | CacheBudgetForum merged CacheReviewLunch and OPS_CACHE_EVENT for catering. | CACHE_PREVIEW_DAY and CacheVenueBoard discussed bus routes for guests.

- The degradation probe uses the broad query "caching" with a manually linked topic seed so expansion can traverse co-claim entities.
- False positives come from noise identifiers that share the same broad caching seed but are operationally irrelevant.

## Test 3: Latency Impact

Without auto extraction: avg 4.845ms, p50 4.787ms, p95 5.375ms, p99 6.122ms

With auto extraction: avg 13.297ms, p50 12.979ms, p95 15.635ms, p99 16.762ms

Delta: avg 8.452ms, p50 8.192ms, p95 10.26ms, p99 10.64ms

Average delta <10ms: true

## Test 4: LLM Extraction Quality

Skipped: Ollama was not reachable at http://localhost:11434/v1/models within 1.5s.

## Test 5: End-to-End Graph Growth

Meaningful growth observed: true

| Claims | Entities | Relations | Components | Largest component | Coverage | Isolated | Avg degree |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 10 | 14 | 22 | 1 | 14 | 1 | 0 | 3.143 |
| 20 | 17 | 45 | 1 | 17 | 1 | 0 | 4.471 |
| 30 | 20 | 79 | 1 | 20 | 1 | 0 | 5.7 |

- Connectivity is computed on the entity relation graph, not the bipartite claim-entity links.
- A growing largest component is treated as evidence that the graph is consolidating shared concepts instead of only adding disconnected noise.

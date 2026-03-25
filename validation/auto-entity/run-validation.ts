#!/usr/bin/env node

import { promises as fs } from 'node:fs';
import path from 'node:path';
import { performance } from 'node:perf_hooks';

import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import { defaultPolicy } from '@pce/policy-schemas';
import { stringify } from 'yaml';

import {
  handleActivate,
  handlePolicyApply,
  handleUpsert,
  type ToolResult,
} from '../../apps/pce-memory/src/core/handlers';
import {
  closeDb,
  getConnection,
  initDb,
  initSchema,
  resetDbAsync,
} from '../../apps/pce-memory/src/db/connection';
import { extractEntities } from '../../apps/pce-memory/src/store/entityExtractor';
import {
  extractEntitiesWithLLM,
  type EntityCandidate as LlmEntityCandidate,
} from '../../apps/pce-memory/src/store/llmEntityExtractor';
import {
  linkClaimEntity,
  queryEntities,
  upsertEntity,
  type EntityInput,
} from '../../apps/pce-memory/src/store/entities';
import { setEmbeddingService } from '../../apps/pce-memory/src/store/hybridSearch';
import { resetLayerScopeState } from '../../apps/pce-memory/src/state/layerScopeState';
import { resetMemoryState } from '../../apps/pce-memory/src/state/memoryState';
import { initRateState, resetRates } from '../../apps/pce-memory/src/store/rate';

const REPO_ROOT = process.cwd();
const RESULTS_DIR = path.join(REPO_ROOT, 'validation/auto-entity/results');
const RESULTS_JSON_PATH = path.join(RESULTS_DIR, 'results.json');
const REPORT_PATH = path.join(RESULTS_DIR, 'report.md');
const ALLOW_TAGS = ['answer:task'];
const BASE_TIME = Date.parse('2026-03-25T00:00:00.000Z');
const LATENCY_CONTROL_ENTITY = createTopicSeed('Latency Control', 'latency-control');
const CACHING_SEED = createTopicSeed('Caching', 'caching');

type ToolResultLike = ToolResult & {
  structuredContent?: Record<string, unknown>;
  content?: Array<{ type?: string; text?: string }>;
};

type UpsertPayload = {
  id: string;
  is_new: boolean;
};

type ActivatePayload = {
  claims: Array<{
    claim: {
      id: string;
      text: string;
      content_hash: string;
    };
    score: number;
  }>;
};

type TopicSpec = {
  query: string;
  label: string;
  seed: EntityInput;
  claims: string[];
};

type QueryMetric = {
  query: string;
  label: string;
  p_at_3: number;
  hits: number;
  relevant_pool: number;
  top_claim_texts: string[];
};

type QueryExpansionTestResult = {
  average_p_at_3: number;
  baseline: QueryMetric[];
  expanded_with_auto_entities: QueryMetric[];
  delta_p_at_3: number;
  notes: string[];
};

type ExpectedGroup = readonly string[];

type NoiseClaimSpec = {
  id: string;
  text: string;
  expected_groups: readonly ExpectedGroup[];
  manual_seed?: EntityInput;
};

type EntityClassification = {
  total_instances: number;
  relevant_instances: number;
  noise_instances: number;
  total_unique: number;
  relevant_unique: number;
  noise_unique: number;
};

type NoiseDegradationMetric = {
  p_at_3: number;
  false_positives: number;
  top_claim_texts: string[];
};

type NoiseTestResult = {
  extracted_entities: EntityClassification;
  clean_control: NoiseDegradationMetric;
  noisy_corpus: NoiseDegradationMetric;
  degradation_observed: boolean;
  notes: string[];
};

type LatencyStats = {
  avg_ms: number;
  p50_ms: number;
  p95_ms: number;
  p99_ms: number;
};

type LatencyTestResult = {
  baseline_without_auto_extraction: LatencyStats;
  with_auto_extraction: LatencyStats;
  delta_ms: LatencyStats;
  avg_delta_below_10ms: boolean;
};

type OllamaRuntime = {
  endpoint: string;
  model: string;
};

type ExtractionQualityMetric = {
  extractor: 'pattern-nlp' | 'llm';
  total_entities: number;
  matched_entities: number;
  noise_entities: number;
  expected_groups: number;
  matched_groups: number;
  avg_entities_per_claim: number;
  precision: number;
  recall: number;
};

type LlmTestResult =
  | {
      skipped: true;
      reason: string;
    }
  | {
      skipped: false;
      runtime: OllamaRuntime;
      pattern: ExtractionQualityMetric;
      llm: ExtractionQualityMetric;
      notes: string[];
    };

type GraphBatchMetric = {
  batch_size: number;
  entity_count: number;
  relation_count: number;
  component_count: number;
  largest_component_size: number;
  largest_component_coverage: number;
  isolated_entity_count: number;
  average_degree: number;
  relation_per_entity: number;
};

type GraphGrowthResult = {
  batches: GraphBatchMetric[];
  meaningful_growth: boolean;
  notes: string[];
};

type ValidationResults = {
  generated_at: string;
  environment: {
    cwd: string;
    node: string;
  };
  assumptions: string[];
  tests: {
    query_expansion_improvement: QueryExpansionTestResult;
    pattern_nlp_noise: NoiseTestResult;
    latency_impact: LatencyTestResult;
    llm_extraction_quality: LlmTestResult;
    end_to_end_graph_growth: GraphGrowthResult;
  };
};

function parseToolContent(result: ToolResultLike): Record<string, unknown> {
  const text = result.content
    ?.map((entry) => entry.text)
    .filter((value): value is string => typeof value === 'string')
    .join('\n')
    .trim();
  if (!text) {
    return {};
  }
  try {
    return JSON.parse(text) as Record<string, unknown>;
  } catch {
    return { text };
  }
}

function expectSuccess<T extends Record<string, unknown>>(result: ToolResultLike): T {
  if (result.isError === true) {
    throw new Error(
      `Tool returned error: ${JSON.stringify(result.structuredContent ?? parseToolContent(result), null, 2)}`
    );
  }
  return (result.structuredContent ?? parseToolContent(result)) as T;
}

function normalizeForEmbedding(text: string): string {
  return text
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/[_./:-]+/g, ' ')
    .toLowerCase();
}

function tokenize(text: string): string[] {
  return normalizeForEmbedding(text).match(/[a-z0-9]+/g) ?? [];
}

function fnv1a(input: string): number {
  let hash = 0x811c9dc5;
  for (let index = 0; index < input.length; index++) {
    hash ^= input.charCodeAt(index);
    hash = Math.imul(hash, 0x01000193);
  }
  return hash >>> 0;
}

function deterministicEmbedding(text: string, dimensions = 64): readonly number[] {
  const vector = new Array<number>(dimensions).fill(0);
  const tokens = tokenize(text);
  if (tokens.length === 0) {
    vector[0] = 1;
    return vector;
  }

  for (const token of tokens) {
    const baseHash = fnv1a(token);
    const index = baseHash % dimensions;
    const sign = (fnv1a(`${token}:sign`) & 1) === 0 ? 1 : -1;
    vector[index] += sign;
  }

  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    vector[0] = 1;
    return vector;
  }

  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createDeterministicEmbeddingService(): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      async () =>
        ({
          _tag: 'Right',
          right: {
            embedding: deterministicEmbedding(text),
            modelVersion: 'deterministic-bow-v1',
          },
        }) as Awaited<ReturnType<ReturnType<EmbeddingService['embed']>>>,
  };
}

function normalizeMatchKey(value: string): string {
  return value
    .trim()
    .toLowerCase()
    .replace(/[^a-z0-9/.-]+/g, '-')
    .replace(/-+/g, '-')
    .replace(/^-+|-+$/g, '');
}

function squashMatchKey(value: string): string {
  return normalizeMatchKey(value).replace(/[-/.]+/g, '');
}

function matchesExpectedGroup(value: string, group: readonly string[]): boolean {
  const normalized = normalizeMatchKey(value);
  const squashed = squashMatchKey(value);
  return group.some((candidate) => {
    const expected = normalizeMatchKey(candidate);
    return normalized === expected || squashed === squashMatchKey(candidate);
  });
}

function createTopicSeed(name: string, canonicalKey: string): EntityInput {
  return {
    id: `ent_topic_${canonicalKey.replace(/[^a-z0-9]+/g, '_')}`,
    type: 'Concept',
    name,
    canonical_key: canonicalKey,
  };
}

function buildPolicyYaml(options: {
  queryExpansionEnabled: boolean;
  maxSeedEntities?: number;
  maxRelatedEntities?: number;
  maxExpansionTerms?: number;
  llmEnabled?: boolean;
  ollamaEndpoint?: string;
  model?: string;
}): string {
  return stringify({
    ...defaultPolicy,
    retrieval: {
      ...(defaultPolicy.retrieval ?? {}),
      hybrid: {
        ...(defaultPolicy.retrieval?.hybrid ?? {}),
        query_expansion: {
          enabled: options.queryExpansionEnabled,
          max_seed_entities: options.maxSeedEntities ?? 1,
          max_related_entities: options.maxRelatedEntities ?? 12,
          max_expansion_terms: options.maxExpansionTerms ?? 12,
        },
      },
    },
    extraction: {
      ...(defaultPolicy.extraction ?? {}),
      llm_enabled: options.llmEnabled ?? false,
      ...(options.ollamaEndpoint ? { ollama_endpoint: options.ollamaEndpoint } : {}),
      ...(options.model ? { model: options.model } : {}),
    },
  });
}

async function setupIsolatedStore(options: {
  queryExpansionEnabled: boolean;
  llmEnabled?: boolean;
  ollamaEndpoint?: string;
  model?: string;
}): Promise<void> {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env['PCE_DB'] = ':memory:';
  process.env['PCE_RATE_CAP'] = '1000000';
  process.env['PCE_RATE_WINDOW'] = '0';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  setEmbeddingService(createDeterministicEmbeddingService());
  expectSuccess(
    await handlePolicyApply({
      yaml: buildPolicyYaml(options),
    })
  );
}

function buildProvenance(index: number) {
  return {
    at: new Date(BASE_TIME + index * 60_000).toISOString(),
    actor: 'codex',
    note: 'auto entity validation',
  };
}

type SeedStrategy = 'auto' | 'manual_only' | 'auto_with_manual_seed';

async function upsertProjectClaim(
  text: string,
  index: number,
  strategy: SeedStrategy,
  manualSeed?: EntityInput
): Promise<string> {
  const upsertArgs: Record<string, unknown> = {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: buildProvenance(index),
  };
  if (strategy === 'manual_only' && manualSeed) {
    upsertArgs['entities'] = [manualSeed];
  }

  const upserted = expectSuccess<UpsertPayload>(await handleUpsert(upsertArgs));
  if (strategy === 'auto_with_manual_seed' && manualSeed) {
    const entity = await upsertEntity(manualSeed);
    await linkClaimEntity(upserted.id, entity.id);
  }

  return upserted.id;
}

async function activateTopClaims(
  query: string,
  topK: number = 3
): Promise<ActivatePayload['claims']> {
  const activated = expectSuccess<ActivatePayload>(
    await handleActivate({
      scope: ['project'],
      allow: ALLOW_TAGS,
      top_k: topK,
      q: query,
    })
  );
  return activated.claims;
}

function precisionAtK(ids: readonly string[], relevantIds: ReadonlySet<string>, k: number): number {
  let hits = 0;
  for (const id of ids.slice(0, k)) {
    if (relevantIds.has(id)) {
      hits++;
    }
  }
  return hits / k;
}

function average(values: readonly number[]): number {
  if (values.length === 0) return 0;
  return values.reduce((sum, value) => sum + value, 0) / values.length;
}

function percentile(values: readonly number[], quantile: number): number {
  if (values.length === 0) {
    return 0;
  }
  const sorted = [...values].sort((left, right) => left - right);
  const index = Math.min(sorted.length - 1, Math.max(0, Math.ceil(sorted.length * quantile) - 1));
  return sorted[index] ?? 0;
}

function round(value: number, digits: number = 3): number {
  return Number(value.toFixed(digits));
}

async function listAutoEntityKeysForClaim(claimId: string): Promise<string[]> {
  const entities = await queryEntities({ claim_id: claimId, limit: 100 });
  return entities
    .filter((entity) => entity.id.startsWith('ent_auto_'))
    .map((entity) => entity.canonical_key ?? entity.name)
    .filter((value): value is string => typeof value === 'string' && value.length > 0);
}

async function runQueryExpansionImprovementTest(): Promise<QueryExpansionTestResult> {
  const topics: TopicSpec[] = [
    {
      query: 'authentication',
      label: 'Authentication',
      seed: createTopicSeed('Authentication', 'authentication'),
      claims: [
        'JWT rotation protects access tokens during mobile sign in recovery.',
        'SessionManager closes stale refresh grants after logout.',
        'OAuthClient validates PKCE verifier state before token exchange.',
        'AccessPolicyService records MFA checkpoint failures for sign in.',
      ],
    },
    {
      query: 'caching',
      label: 'Caching',
      seed: createTopicSeed('Caching', 'caching'),
      claims: [
        'RedisCache stores rendered dashboard fragments with key bucketing.',
        'CacheWarmer preloads hot keys during deploy cutovers.',
        'CACHE_TTL_SECONDS controls eviction timing for catalog pages.',
        'EdgeCachePolicy bypasses stale entries during purge storms.',
      ],
    },
    {
      query: 'synchronization',
      label: 'Synchronization',
      seed: createTopicSeed('Synchronization', 'synchronization'),
      claims: [
        'CRDT merge clocks reconcile offline edits after reconnect.',
        'SyncCursor checkpoints replica positions after batch upload.',
        'ReplicaScheduler defers backfill retries during congestion.',
        'ConflictResolver compares vector clocks before commit.',
      ],
    },
    {
      query: 'schema',
      label: 'Schema',
      seed: createTopicSeed('Schema', 'schema'),
      claims: [
        'DuckDB migration planner validates nullable columns before release.',
        'SchemaMigrator replays db/schema.sql during bootstrap.',
        'ColumnBackfillJob updates historic rows without table rewrites.',
        'IndexReviewBoard tracks breaking DDL before rollout.',
      ],
    },
    {
      query: 'testing',
      label: 'Testing',
      seed: createTopicSeed('Testing', 'testing'),
      claims: [
        'Vitest covers handleActivate ranking with deterministic embeddings.',
        'ContractHarness snapshots MCP tool payloads for regression checks.',
        'FakeClockDriver advances retention windows in unit suites.',
        'apps/pce-memory/src/core/handlers.ts hosts activate validation helpers.',
      ],
    },
  ];

  async function seedScenario(strategy: SeedStrategy) {
    const relevantByQuery = new Map<string, string[]>();
    const textById = new Map<string, string>();
    let claimIndex = 0;

    for (let roundIndex = 0; roundIndex < 4; roundIndex++) {
      for (const topic of topics) {
        const text = topic.claims[roundIndex]!;
        const claimId = await upsertProjectClaim(text, claimIndex++, strategy, topic.seed);
        relevantByQuery.set(topic.query, [...(relevantByQuery.get(topic.query) ?? []), claimId]);
        textById.set(claimId, text);
      }
    }

    const metrics: QueryMetric[] = [];
    for (const topic of topics) {
      const claims = await activateTopClaims(topic.query, 3);
      const ids = claims.map((entry) => entry.claim.id);
      const relevantIds = new Set(relevantByQuery.get(topic.query) ?? []);
      metrics.push({
        query: topic.query,
        label: topic.label,
        p_at_3: round(precisionAtK(ids, relevantIds, 3)),
        hits: ids.filter((id) => relevantIds.has(id)).length,
        relevant_pool: relevantIds.size,
        top_claim_texts: ids.map((id) => textById.get(id) ?? id),
      });
    }

    return metrics;
  }

  await setupIsolatedStore({ queryExpansionEnabled: true });
  const baseline = await seedScenario('manual_only');

  await setupIsolatedStore({ queryExpansionEnabled: true });
  const expanded = await seedScenario('auto_with_manual_seed');

  const baselineAverage = round(average(baseline.map((item) => item.p_at_3)));
  const expandedAverage = round(average(expanded.map((item) => item.p_at_3)));

  return {
    average_p_at_3: expandedAverage,
    baseline,
    expanded_with_auto_entities: expanded,
    delta_p_at_3: round(expandedAverage - baselineAverage),
    notes: [
      'Broad seed entities were manually linked so queries like "authentication" and "caching" had a stable graph entry point.',
      'The measured delta comes from the presence or absence of auto-extracted sibling entities that query expansion can traverse.',
    ],
  };
}

function buildNoiseClaims(): NoiseClaimSpec[] {
  const coreClaims: NoiseClaimSpec[] = [
    {
      id: 'auth-1',
      text: 'JWT access tokens rotate after incident drills.',
      expected_groups: [['jwt']],
    },
    {
      id: 'auth-2',
      text: 'AuthGateway records login retries for fraud review.',
      expected_groups: [['authgateway']],
    },
    { id: 'sync-1', text: 'CRDT replicas merge after offline edits.', expected_groups: [['crdt']] },
    {
      id: 'sync-2',
      text: 'SyncCursor stores replica offsets before batch upload.',
      expected_groups: [['synccursor']],
    },
    {
      id: 'schema-1',
      text: 'DuckDB checkpoints compact vectors before backup.',
      expected_groups: [['duckdb']],
    },
    {
      id: 'schema-2',
      text: 'SchemaMigrator replays db/schema.sql before deployment.',
      expected_groups: [['schemamigrator'], ['db/schema.sql']],
    },
    {
      id: 'test-1',
      text: 'Vitest snapshots guard activate payload regressions.',
      expected_groups: [['vitest']],
    },
    {
      id: 'test-2',
      text: 'apps/pce-memory/src/core/handlers.ts validates upsert input.',
      expected_groups: [['apps/pce-memory/src/core/handlers.ts']],
    },
    {
      id: 'build-1',
      text: 'pnpm workspace filters limit package rebuilds.',
      expected_groups: [['pnpm']],
    },
    {
      id: 'build-2',
      text: 'tsx powers maintenance scripts during local debugging.',
      expected_groups: [['tsx']],
    },
    {
      id: 'cache-good-1',
      text: 'RedisCache keeps fragment payloads hot across shard moves.',
      expected_groups: [['rediscache']],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-good-2',
      text: 'CacheWarmer preloads catalog keys before traffic spikes.',
      expected_groups: [['cachewarmer']],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-good-3',
      text: 'CACHE_TTL_SECONDS limits stale widget exposure after purge.',
      expected_groups: [['cache-ttl-seconds', 'cache_ttl_seconds']],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-good-4',
      text: 'EdgeCachePolicy bypasses stale fragments during rollback.',
      expected_groups: [['edgecachepolicy']],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'mixed-1',
      text: 'JWT review referenced CacheStandup2026 lunch planning.',
      expected_groups: [['jwt']],
    },
    {
      id: 'mixed-2',
      text: 'DuckDB migration notes sat beside RoadmapSyncBoard venue details.',
      expected_groups: [['duckdb']],
    },
    {
      id: 'mixed-3',
      text: 'Vitest checks were mentioned in BudgetLaunchBoard staffing notes.',
      expected_groups: [['vitest']],
    },
    {
      id: 'mixed-4',
      text: 'CRDT conflict replay appeared next to OKRReviewBoard catering logistics.',
      expected_groups: [['crdt']],
    },
    {
      id: 'mixed-5',
      text: 'SchemaMigrator reused CACHE_PREVIEW_DAY staffing spreadsheets.',
      expected_groups: [['schemamigrator']],
    },
  ];

  const noiseOnlyTokens = [
    'LaunchDeckBoard',
    'BudgetSyncBoard',
    'RoadmapTownHall',
    'HiringPlanHub',
    'RetentionReviewBoard',
    'EnablementSprintBoard',
    'TravelRosterHub',
    'QBRSummaryBoard',
    'BrandRefreshCouncil',
    'MenuPlanningBoard',
    'VendorOpsCouncil',
    'PilotLaunchForum',
    'CustomerDinnerBoard',
    'FieldEventHub',
    'HolidayShiftBoard',
  ];

  const pureNoiseClaims = noiseOnlyTokens.map((token, index) => ({
    id: `noise-${index + 1}`,
    text: `${token} reviewed seating charts with OPS_SUMMARY_${index + 10} for quarterly planning.`,
    expected_groups: [] as const,
  }));

  const cachingNoiseClaims: NoiseClaimSpec[] = [
    {
      id: 'cache-noise-1',
      text: 'CacheStandup2026 and CACHE_REVIEW_2026 picked lunch options for visitors.',
      expected_groups: [],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-noise-2',
      text: 'CacheSlideBoard used CacheTownHall notes to confirm swag counts.',
      expected_groups: [],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-noise-3',
      text: 'CACHE_PREVIEW_DAY and CacheVenueBoard discussed bus routes for guests.',
      expected_groups: [],
      manual_seed: CACHING_SEED,
    },
    {
      id: 'cache-noise-4',
      text: 'CacheBudgetForum merged CacheReviewLunch and OPS_CACHE_EVENT for catering.',
      expected_groups: [],
      manual_seed: CACHING_SEED,
    },
  ];

  const mixedNoiseTokens = [
    'CacheStandup2026',
    'RoadmapHallBoard',
    'VendorPrepCouncil',
    'SupportShiftBoard',
    'RiskOpsForum',
    'RegionalLaunchHub',
    'StaffingSyncBoard',
    'BudgetPreviewCouncil',
    'EventLogisticsHub',
    'QABriefingBoard',
    'EnablementLunchBoard',
  ];

  const mixedTemplates: Array<{ prefix: string; expected_groups: readonly ExpectedGroup[] }> = [
    { prefix: 'pnpm workspace tasks landed next to', expected_groups: [['pnpm']] },
    { prefix: 'tsx maintenance scripts were cited beside', expected_groups: [['tsx']] },
    { prefix: 'AuthGateway retries appeared beside', expected_groups: [['authgateway']] },
    { prefix: 'SyncCursor lag metrics sat next to', expected_groups: [['synccursor']] },
    {
      prefix: 'apps/pce-memory/src/core/handlers.ts was referenced beside',
      expected_groups: [['apps/pce-memory/src/core/handlers.ts']],
    },
    { prefix: 'DuckDB checkpoint output was attached beside', expected_groups: [['duckdb']] },
    { prefix: 'Vitest failures were pasted next to', expected_groups: [['vitest']] },
    { prefix: 'SchemaMigrator logs were copied beside', expected_groups: [['schemamigrator']] },
    { prefix: 'CRDT repair notes were grouped beside', expected_groups: [['crdt']] },
    { prefix: 'JWT revoke details were posted beside', expected_groups: [['jwt']] },
    { prefix: 'CacheWarmer metrics were shown beside', expected_groups: [['cachewarmer']] },
  ];

  const mixedClaims = mixedTemplates.map((template, index) => ({
    id: `mixed-${index + 6}`,
    text: `${template.prefix} ${mixedNoiseTokens[index]!} and MIXED_NOTE_${index + 1}.`,
    expected_groups: template.expected_groups,
  }));

  return [...coreClaims, ...pureNoiseClaims, ...cachingNoiseClaims, ...mixedClaims];
}

async function classifyExtractedEntities(
  claims: readonly NoiseClaimSpec[],
  strategy: SeedStrategy
): Promise<{
  classification: EntityClassification;
  relevantCachingIds: string[];
}> {
  const relevantUnique = new Set<string>();
  const noiseUnique = new Set<string>();
  let relevantInstances = 0;
  let noiseInstances = 0;
  const relevantCachingIds: string[] = [];

  let claimIndex = 0;
  for (const claim of claims) {
    const claimId = await upsertProjectClaim(claim.text, claimIndex++, strategy, claim.manual_seed);
    const extractedKeys = await listAutoEntityKeysForClaim(claimId);
    const normalizedGroups = claim.expected_groups.map((group) => group.map(normalizeMatchKey));
    for (const key of extractedKeys) {
      const matched = normalizedGroups.some((group) => matchesExpectedGroup(key, group));
      if (matched) {
        relevantInstances++;
        relevantUnique.add(normalizeMatchKey(key));
      } else {
        noiseInstances++;
        noiseUnique.add(normalizeMatchKey(key));
      }
    }

    if (claim.manual_seed?.canonical_key === 'caching' && claim.expected_groups.length > 0) {
      relevantCachingIds.push(claimId);
    }
  }

  return {
    classification: {
      total_instances: relevantInstances + noiseInstances,
      relevant_instances: relevantInstances,
      noise_instances: noiseInstances,
      total_unique: relevantUnique.size + noiseUnique.size,
      relevant_unique: relevantUnique.size,
      noise_unique: noiseUnique.size,
    },
    relevantCachingIds,
  };
}

async function evaluateCachingNoiseDegradation(
  claims: readonly NoiseClaimSpec[]
): Promise<NoiseTestResult> {
  const relevantCachingFilter = (claim: NoiseClaimSpec) =>
    claim.manual_seed?.canonical_key === 'caching' && claim.expected_groups.length > 0;
  const noisyCachingFilter = (claim: NoiseClaimSpec) =>
    claim.manual_seed?.canonical_key === 'caching' && claim.expected_groups.length === 0;

  await setupIsolatedStore({ queryExpansionEnabled: true });
  const cleanClaims = claims.filter((claim) => !noisyCachingFilter(claim));
  const cleanOutcome = await classifyExtractedEntities(cleanClaims, 'auto_with_manual_seed');
  const cleanActivate = await activateTopClaims('caching', 3);
  const cleanRelevant = new Set(cleanOutcome.relevantCachingIds);
  const cleanIds = cleanActivate.map((entry) => entry.claim.id);

  await setupIsolatedStore({ queryExpansionEnabled: true });
  const noisyOutcome = await classifyExtractedEntities(claims, 'auto_with_manual_seed');
  const noisyActivate = await activateTopClaims('caching', 3);
  const noisyRelevant = new Set(noisyOutcome.relevantCachingIds);
  const noisyIds = noisyActivate.map((entry) => entry.claim.id);
  const noisyFalsePositives = noisyIds.filter((id) => !noisyRelevant.has(id)).length;

  return {
    extracted_entities: noisyOutcome.classification,
    clean_control: {
      p_at_3: round(precisionAtK(cleanIds, cleanRelevant, 3)),
      false_positives: cleanIds.filter((id) => !cleanRelevant.has(id)).length,
      top_claim_texts: cleanActivate.map((entry) => entry.claim.text),
    },
    noisy_corpus: {
      p_at_3: round(precisionAtK(noisyIds, noisyRelevant, 3)),
      false_positives: noisyFalsePositives,
      top_claim_texts: noisyActivate.map((entry) => entry.claim.text),
    },
    degradation_observed:
      precisionAtK(noisyIds, noisyRelevant, 3) < precisionAtK(cleanIds, cleanRelevant, 3),
    notes: [
      'The degradation probe uses the broad query "caching" with a manually linked topic seed so expansion can traverse co-claim entities.',
      'False positives come from noise identifiers that share the same broad caching seed but are operationally irrelevant.',
    ],
  };
}

async function runPatternNlpNoiseTest(): Promise<NoiseTestResult> {
  const claims = buildNoiseClaims();
  return evaluateCachingNoiseDegradation(claims);
}

function buildLatencyTexts(count: number): string[] {
  return Array.from({ length: count }, (_, index) => {
    const number = index + 1;
    return `JWT AuthFlow${number} coordinates TypeScript Vitest checks for rollout ${number}.`;
  });
}

async function measureUpsertLatency(
  texts: readonly string[],
  strategy: SeedStrategy,
  manualSeed?: EntityInput
): Promise<LatencyStats> {
  const samples: number[] = [];
  for (let index = 0; index < texts.length; index++) {
    const startedAt = performance.now();
    await upsertProjectClaim(texts[index]!, index, strategy, manualSeed);
    samples.push(performance.now() - startedAt);
  }

  return {
    avg_ms: round(average(samples)),
    p50_ms: round(percentile(samples, 0.5)),
    p95_ms: round(percentile(samples, 0.95)),
    p99_ms: round(percentile(samples, 0.99)),
  };
}

function diffLatency(left: LatencyStats, right: LatencyStats): LatencyStats {
  return {
    avg_ms: round(right.avg_ms - left.avg_ms),
    p50_ms: round(right.p50_ms - left.p50_ms),
    p95_ms: round(right.p95_ms - left.p95_ms),
    p99_ms: round(right.p99_ms - left.p99_ms),
  };
}

async function runLatencyImpactTest(): Promise<LatencyTestResult> {
  const texts = buildLatencyTexts(100);

  await setupIsolatedStore({ queryExpansionEnabled: false });
  const baseline = await measureUpsertLatency(texts, 'manual_only', LATENCY_CONTROL_ENTITY);

  await setupIsolatedStore({ queryExpansionEnabled: false });
  const auto = await measureUpsertLatency(texts, 'auto');

  const delta = diffLatency(baseline, auto);
  return {
    baseline_without_auto_extraction: baseline,
    with_auto_extraction: auto,
    delta_ms: delta,
    avg_delta_below_10ms: delta.avg_ms < 10,
  };
}

async function resolveOllamaRuntime(): Promise<OllamaRuntime | null> {
  const endpoint = process.env['PCE_TEST_OLLAMA_ENDPOINT'] ?? 'http://localhost:11434';
  const preferredModel = process.env['PCE_TEST_OLLAMA_MODEL'];
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 1_500);

  try {
    const response = await fetch(`${endpoint.replace(/\/+$/g, '')}/v1/models`, {
      signal: controller.signal,
    });
    if (!response.ok) {
      return null;
    }

    const payload = (await response.json()) as { data?: Array<{ id?: string }> };
    const modelIds = (payload.data ?? [])
      .map((item) => item.id)
      .filter((id): id is string => typeof id === 'string' && id.length > 0);
    if (modelIds.length === 0) {
      return null;
    }

    return {
      endpoint,
      model: preferredModel && modelIds.includes(preferredModel) ? preferredModel : modelIds[0]!,
    };
  } catch {
    return null;
  } finally {
    clearTimeout(timeout);
  }
}

type QualityClaimSpec = {
  text: string;
  expected_groups: readonly ExpectedGroup[];
};

function buildLlmQualityClaims(): QualityClaimSpec[] {
  return [
    {
      text: 'Authentication architecture uses JWT access tokens, refresh token rotation, and session revocation.',
      expected_groups: [
        ['authentication'],
        ['jwt'],
        ['refresh-token', 'refresh-token-rotation'],
        ['session-revocation'],
      ],
    },
    {
      text: 'Synchronization relies on CRDT replicas, vector clocks, and offline conflict resolution.',
      expected_groups: [
        ['synchronization'],
        ['crdt'],
        ['vector-clocks', 'vector-clock'],
        ['offline-conflict-resolution', 'conflict-resolution'],
      ],
    },
    {
      text: 'Schema rollout keeps DuckDB migration plans and nullable column audits together.',
      expected_groups: [
        ['schema'],
        ['duckdb'],
        ['migration-plan', 'migration-plans'],
        ['nullable-column-audit', 'nullable-column-audits'],
      ],
    },
    {
      text: 'Testing combines Vitest snapshot baselines and a contract harness for MCP payloads.',
      expected_groups: [
        ['testing'],
        ['vitest'],
        ['snapshot-baselines', 'snapshot-baseline'],
        ['contract-harness'],
        ['mcp'],
      ],
    },
    {
      text: 'Build automation uses pnpm workspaces and tsx scripts for release validation.',
      expected_groups: [['pnpm'], ['workspace', 'workspaces'], ['tsx'], ['release-validation']],
    },
    {
      text: 'OAuthClient validates the PKCE verifier before token exchange for browser sign in.',
      expected_groups: [['oauthclient', 'oauth-client'], ['pkce'], ['token-exchange']],
    },
    {
      text: 'EventStoreWriter replays checkpoints into DuckDB during disaster recovery drills.',
      expected_groups: [
        ['eventstorewriter', 'event-store-writer'],
        ['checkpoint-replay', 'checkpoints'],
        ['duckdb'],
        ['disaster-recovery'],
      ],
    },
    {
      text: 'The MCP tool handler writes active context records under the retrieval policy.',
      expected_groups: [['mcp'], ['tool-handler'], ['active-context'], ['retrieval-policy']],
    },
    {
      text: 'CacheWarmer coordinates cache invalidation and edge cache updates after deploys.',
      expected_groups: [['cachewarmer', 'cache-warmer'], ['cache-invalidation'], ['edge-cache']],
    },
    {
      text: 'SchemaMigrator opens a rollback window behind a feature flag during release.',
      expected_groups: [
        ['schemamigrator', 'schema-migrator'],
        ['rollback-window'],
        ['feature-flag'],
        ['release'],
      ],
    },
  ];
}

function countQualityMatches(
  entities: readonly string[],
  expectedGroups: readonly ExpectedGroup[]
): { matchedEntities: number; noiseEntities: number; matchedGroups: number } {
  let matchedEntities = 0;
  let noiseEntities = 0;
  let matchedGroups = 0;
  const hitGroups = new Set<number>();

  for (const entity of entities) {
    let matched = false;
    for (let index = 0; index < expectedGroups.length; index++) {
      if (matchesExpectedGroup(entity, expectedGroups[index]!)) {
        matched = true;
        hitGroups.add(index);
      }
    }
    if (matched) {
      matchedEntities++;
    } else {
      noiseEntities++;
    }
  }

  matchedGroups = hitGroups.size;
  return { matchedEntities, noiseEntities, matchedGroups };
}

async function evaluateExtractionQuality(
  claims: readonly QualityClaimSpec[],
  extractor: 'pattern-nlp' | 'llm',
  runtime?: OllamaRuntime
): Promise<ExtractionQualityMetric> {
  let totalEntities = 0;
  let matchedEntities = 0;
  let noiseEntities = 0;
  let expectedGroups = 0;
  let matchedGroups = 0;

  for (const claim of claims) {
    const extracted =
      extractor === 'pattern-nlp'
        ? extractEntities(claim.text).map((entity) => entity.canonical_key)
        : (
            await extractEntitiesWithLLM(claim.text, {
              ollamaEndpoint: runtime?.endpoint,
              model: runtime?.model,
            })
          ).entities.map((entity: LlmEntityCandidate) => entity.canonical_key);

    const match = countQualityMatches(extracted, claim.expected_groups);
    totalEntities += extracted.length;
    matchedEntities += match.matchedEntities;
    noiseEntities += match.noiseEntities;
    expectedGroups += claim.expected_groups.length;
    matchedGroups += match.matchedGroups;
  }

  return {
    extractor,
    total_entities: totalEntities,
    matched_entities: matchedEntities,
    noise_entities: noiseEntities,
    expected_groups: expectedGroups,
    matched_groups: matchedGroups,
    avg_entities_per_claim: round(totalEntities / claims.length),
    precision: round(totalEntities === 0 ? 0 : matchedEntities / totalEntities),
    recall: round(expectedGroups === 0 ? 0 : matchedGroups / expectedGroups),
  };
}

async function runLlmExtractionQualityTest(): Promise<LlmTestResult> {
  const runtime = await resolveOllamaRuntime();
  if (!runtime) {
    return {
      skipped: true,
      reason: 'Ollama was not reachable at http://localhost:11434/v1/models within 1.5s.',
    };
  }

  const claims = buildLlmQualityClaims();
  const pattern = await evaluateExtractionQuality(claims, 'pattern-nlp');
  const llm = await evaluateExtractionQuality(claims, 'llm', runtime);

  return {
    skipped: false,
    runtime,
    pattern,
    llm,
    notes: [
      'This compares store-level extractors directly because the current upsert path only runs pattern extraction automatically.',
      'Quality is scored against a synthetic gold set of expected entity groups for each claim.',
    ],
  };
}

function buildGraphGrowthClaims(): string[] {
  return [
    'TypeScript AuthGateway signs JWT access tokens.',
    'JWT rotation metrics flow through Vitest AuthHarness.',
    'DuckDB stores AuthGateway audit snapshots.',
    'TypeScript SyncCursor checkpoints CRDT replicas.',
    'CRDT merge tests run in Vitest SyncHarness.',
    'DuckDB replay validates SyncCursor migrations.',
    'pnpm scripts invoke tsx to backfill DuckDB indexes.',
    'Vitest snapshots cover apps/pce-memory/src/core/handlers.ts activate flows.',
    'TypeScript SchemaMigrator reads db/schema.sql before release.',
    'SchemaMigrator and DuckDB coordinate rollback rehearsals.',
    'pnpm workspace tasks run Vitest and tsx smoke suites.',
    'AuthGateway in TypeScript emits JWT refresh telemetry.',
    'CRDT replica repair persists state in DuckDB.',
    'SchemaMigrator validates apps/pce-memory/src/core/handlers.ts schema hooks.',
    'Vitest ContractHarness checks TypeScript MCP payloads.',
    'DuckDB and pnpm logs feed CacheWarmer diagnostics.',
    'JWT revoke jobs call tsx maintenance scripts.',
    'SyncCursor and SchemaMigrator share db/schema.sql fixtures.',
    'CacheWarmer primes DuckDB query snapshots.',
    'Vitest verifies CacheWarmer fallback behavior.',
    'AuthGateway and CacheWarmer coordinate JWT session eviction.',
    'TypeScript ReplicaScheduler escalates CRDT repair alarms.',
    'DuckDB stores CacheWarmer hit histograms for Vitest replay.',
    'pnpm rebuilds TypeScript ContractHarness packages before test runs.',
    'SchemaMigrator and ReplicaScheduler replay db/schema.sql drift corrections.',
    'tsx scripts compact DuckDB WAL after AuthGateway rollouts.',
    'Vitest RegressionHarness snapshots JWT and CRDT edge cases.',
    'CacheWarmer updates apps/pce-memory/src/core/handlers.ts fixture paths.',
    'ContractHarness publishes pnpm task traces for TypeScript analysis.',
    'DuckDB, SchemaMigrator, and Vitest finalize rollback certification.',
  ];
}

async function collectGraphBatchMetric(batchSize: number): Promise<GraphBatchMetric> {
  const conn = await getConnection();
  const entityReader = await conn.runAndReadAll('SELECT id FROM entities ORDER BY id');
  const relationReader = await conn.runAndReadAll(
    'SELECT src_id, dst_id FROM relations ORDER BY src_id, dst_id'
  );

  const entityIds = (entityReader.getRowObjects() as Array<{ id: string }>).map((row) => row.id);
  const relationRows = relationReader.getRowObjects() as Array<{ src_id: string; dst_id: string }>;
  const adjacency = new Map<string, Set<string>>();
  for (const id of entityIds) {
    adjacency.set(id, new Set());
  }
  for (const relation of relationRows) {
    adjacency.get(relation.src_id)?.add(relation.dst_id);
    adjacency.get(relation.dst_id)?.add(relation.src_id);
  }

  const visited = new Set<string>();
  let componentCount = 0;
  let largestComponentSize = 0;
  let isolatedEntityCount = 0;
  let degreeSum = 0;

  for (const [id, neighbors] of adjacency.entries()) {
    degreeSum += neighbors.size;
    if (neighbors.size === 0) {
      isolatedEntityCount++;
    }
    if (visited.has(id)) {
      continue;
    }

    componentCount++;
    const stack = [id];
    visited.add(id);
    let size = 0;
    while (stack.length > 0) {
      const current = stack.pop()!;
      size++;
      for (const neighbor of adjacency.get(current) ?? []) {
        if (!visited.has(neighbor)) {
          visited.add(neighbor);
          stack.push(neighbor);
        }
      }
    }
    largestComponentSize = Math.max(largestComponentSize, size);
  }

  const entityCount = entityIds.length;
  const relationCount = relationRows.length;

  return {
    batch_size: batchSize,
    entity_count: entityCount,
    relation_count: relationCount,
    component_count: componentCount,
    largest_component_size: largestComponentSize,
    largest_component_coverage: round(entityCount === 0 ? 0 : largestComponentSize / entityCount),
    isolated_entity_count: isolatedEntityCount,
    average_degree: round(entityCount === 0 ? 0 : degreeSum / entityCount),
    relation_per_entity: round(entityCount === 0 ? 0 : relationCount / entityCount),
  };
}

async function runGraphGrowthTest(): Promise<GraphGrowthResult> {
  await setupIsolatedStore({ queryExpansionEnabled: false });

  const claims = buildGraphGrowthClaims();
  const batches: GraphBatchMetric[] = [];

  for (let index = 0; index < claims.length; index++) {
    await upsertProjectClaim(claims[index]!, index, 'auto');
    if ((index + 1) % 10 === 0) {
      batches.push(await collectGraphBatchMetric(index + 1));
    }
  }

  const meaningfulGrowth =
    batches.length === 3 &&
    batches[0]!.entity_count < batches[1]!.entity_count &&
    batches[1]!.entity_count < batches[2]!.entity_count &&
    batches[0]!.relation_count < batches[1]!.relation_count &&
    batches[1]!.relation_count < batches[2]!.relation_count &&
    batches[0]!.largest_component_size < batches[1]!.largest_component_size &&
    batches[1]!.largest_component_size < batches[2]!.largest_component_size &&
    batches[2]!.largest_component_coverage >= 0.4;

  return {
    batches,
    meaningful_growth: meaningfulGrowth,
    notes: [
      'Connectivity is computed on the entity relation graph, not the bipartite claim-entity links.',
      'A growing largest component is treated as evidence that the graph is consolidating shared concepts instead of only adding disconnected noise.',
    ],
  };
}

function formatLatencyStats(stats: LatencyStats): string {
  return `avg ${stats.avg_ms}ms, p50 ${stats.p50_ms}ms, p95 ${stats.p95_ms}ms, p99 ${stats.p99_ms}ms`;
}

function renderQueryMetrics(title: string, metrics: readonly QueryMetric[]): string {
  const lines = [
    `### ${title}`,
    '',
    '| Query | P@3 | Hits | Top 3 claims |',
    '| --- | ---: | ---: | --- |',
  ];
  for (const metric of metrics) {
    lines.push(
      `| ${metric.label} | ${metric.p_at_3} | ${metric.hits}/${metric.relevant_pool} | ${metric.top_claim_texts.join(' <br> ')} |`
    );
  }
  lines.push('');
  return lines.join('\n');
}

function renderGraphTable(batches: readonly GraphBatchMetric[]): string {
  const lines = [
    '| Claims | Entities | Relations | Components | Largest component | Coverage | Isolated | Avg degree |',
    '| ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |',
  ];
  for (const batch of batches) {
    lines.push(
      `| ${batch.batch_size} | ${batch.entity_count} | ${batch.relation_count} | ${batch.component_count} | ${batch.largest_component_size} | ${batch.largest_component_coverage} | ${batch.isolated_entity_count} | ${batch.average_degree} |`
    );
  }
  return lines.join('\n');
}

function buildReport(results: ValidationResults): string {
  const llmSection =
    results.tests.llm_extraction_quality.skipped === true
      ? [
          '## Test 4: LLM Extraction Quality',
          '',
          `Skipped: ${results.tests.llm_extraction_quality.reason}`,
          '',
        ].join('\n')
      : [
          '## Test 4: LLM Extraction Quality',
          '',
          `Runtime: ${results.tests.llm_extraction_quality.runtime.model} @ ${results.tests.llm_extraction_quality.runtime.endpoint}`,
          '',
          '| Extractor | Total entities | Matched entities | Noise entities | Avg entities/claim | Precision | Recall |',
          '| --- | ---: | ---: | ---: | ---: | ---: | ---: |',
          `| Pattern NLP | ${results.tests.llm_extraction_quality.pattern.total_entities} | ${results.tests.llm_extraction_quality.pattern.matched_entities} | ${results.tests.llm_extraction_quality.pattern.noise_entities} | ${results.tests.llm_extraction_quality.pattern.avg_entities_per_claim} | ${results.tests.llm_extraction_quality.pattern.precision} | ${results.tests.llm_extraction_quality.pattern.recall} |`,
          `| LLM | ${results.tests.llm_extraction_quality.llm.total_entities} | ${results.tests.llm_extraction_quality.llm.matched_entities} | ${results.tests.llm_extraction_quality.llm.noise_entities} | ${results.tests.llm_extraction_quality.llm.avg_entities_per_claim} | ${results.tests.llm_extraction_quality.llm.precision} | ${results.tests.llm_extraction_quality.llm.recall} |`,
          '',
          ...results.tests.llm_extraction_quality.notes.map((note) => `- ${note}`),
          '',
        ].join('\n');

  return [
    '# Auto Entity Extraction Validation Report',
    '',
    `Generated at: ${results.generated_at}`,
    '',
    '## Assumptions',
    '',
    ...results.assumptions.map((item) => `- ${item}`),
    '',
    '## Test 1: Query Expansion Improvement',
    '',
    `Average P@3 without auto entities: ${round(
      average(results.tests.query_expansion_improvement.baseline.map((item) => item.p_at_3))
    )}`,
    '',
    `Average P@3 with auto entities: ${results.tests.query_expansion_improvement.average_p_at_3}`,
    '',
    `Delta: ${results.tests.query_expansion_improvement.delta_p_at_3}`,
    '',
    ...results.tests.query_expansion_improvement.notes.map((note) => `- ${note}`),
    '',
    renderQueryMetrics(
      'Without Auto-Extracted Entities',
      results.tests.query_expansion_improvement.baseline
    ),
    renderQueryMetrics(
      'With Auto-Extracted Entities',
      results.tests.query_expansion_improvement.expanded_with_auto_entities
    ),
    '## Test 2: Pattern NLP Noise',
    '',
    `Auto-extracted entity instances: ${results.tests.pattern_nlp_noise.extracted_entities.total_instances}`,
    '',
    `Relevant instances: ${results.tests.pattern_nlp_noise.extracted_entities.relevant_instances}`,
    '',
    `Noise instances: ${results.tests.pattern_nlp_noise.extracted_entities.noise_instances}`,
    '',
    `Unique relevant/noise entities: ${results.tests.pattern_nlp_noise.extracted_entities.relevant_unique}/${results.tests.pattern_nlp_noise.extracted_entities.noise_unique}`,
    '',
    `Clean control P@3 for "caching": ${results.tests.pattern_nlp_noise.clean_control.p_at_3}`,
    '',
    `Noisy corpus P@3 for "caching": ${results.tests.pattern_nlp_noise.noisy_corpus.p_at_3}`,
    '',
    `Degradation observed: ${results.tests.pattern_nlp_noise.degradation_observed}`,
    '',
    `Clean top 3: ${results.tests.pattern_nlp_noise.clean_control.top_claim_texts.join(' | ')}`,
    '',
    `Noisy top 3: ${results.tests.pattern_nlp_noise.noisy_corpus.top_claim_texts.join(' | ')}`,
    '',
    ...results.tests.pattern_nlp_noise.notes.map((note) => `- ${note}`),
    '',
    '## Test 3: Latency Impact',
    '',
    `Without auto extraction: ${formatLatencyStats(results.tests.latency_impact.baseline_without_auto_extraction)}`,
    '',
    `With auto extraction: ${formatLatencyStats(results.tests.latency_impact.with_auto_extraction)}`,
    '',
    `Delta: ${formatLatencyStats(results.tests.latency_impact.delta_ms)}`,
    '',
    `Average delta <10ms: ${results.tests.latency_impact.avg_delta_below_10ms}`,
    '',
    llmSection,
    '## Test 5: End-to-End Graph Growth',
    '',
    `Meaningful growth observed: ${results.tests.end_to_end_graph_growth.meaningful_growth}`,
    '',
    renderGraphTable(results.tests.end_to_end_graph_growth.batches),
    '',
    ...results.tests.end_to_end_graph_growth.notes.map((note) => `- ${note}`),
    '',
  ].join('\n');
}

async function writeResults(results: ValidationResults): Promise<void> {
  await fs.mkdir(RESULTS_DIR, { recursive: true });
  await fs.writeFile(RESULTS_JSON_PATH, `${JSON.stringify(results, null, 2)}\n`, 'utf8');
  await fs.writeFile(REPORT_PATH, buildReport(results), 'utf8');
}

async function main(): Promise<void> {
  const assumptions = [
    'Because the current pattern extractor does not infer abstract seed concepts like "authentication" or "caching", Tests 1 and 2 manually link those broad topic entities and treat the presence of auto-extracted sibling entities as the experimental variable.',
    'Test 4 compares the store-level pattern and LLM extractors directly because automatic LLM extraction is currently wired into distill, not upsert.',
    'All latency and retrieval measurements use a deterministic local embedding service so the experiment is repeatable without external model variance.',
  ];

  const results: ValidationResults = {
    generated_at: new Date().toISOString(),
    environment: {
      cwd: REPO_ROOT,
      node: process.version,
    },
    assumptions,
    tests: {
      query_expansion_improvement: await runQueryExpansionImprovementTest(),
      pattern_nlp_noise: await runPatternNlpNoiseTest(),
      latency_impact: await runLatencyImpactTest(),
      llm_extraction_quality: await runLlmExtractionQualityTest(),
      end_to_end_graph_growth: await runGraphGrowthTest(),
    },
  };

  await writeResults(results);
}

main()
  .catch((error) => {
    console.error(error);
    process.exitCode = 1;
  })
  .finally(async () => {
    try {
      await closeDb();
    } catch {
      // Best-effort cleanup only.
    }
  });

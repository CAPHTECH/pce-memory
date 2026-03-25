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
  initDb,
  initSchema,
  resetDbAsync,
} from '../../apps/pce-memory/src/db/connection';
import { extractEntities } from '../../apps/pce-memory/src/store/entityExtractor';
import {
  extractEntitiesWithLLM,
  type EntityCandidate as LlmEntityCandidate,
  type RelationCandidate as LlmRelationCandidate,
} from '../../apps/pce-memory/src/store/llmEntityExtractor';
import {
  findEntityByCanonicalKey,
  linkClaimEntity,
  upsertEntity,
  type EntityInput,
} from '../../apps/pce-memory/src/store/entities';
import { setEmbeddingService } from '../../apps/pce-memory/src/store/hybridSearch';
import { upsertRelation } from '../../apps/pce-memory/src/store/relations';
import { resetLayerScopeState } from '../../apps/pce-memory/src/state/layerScopeState';
import { resetMemoryState } from '../../apps/pce-memory/src/state/memoryState';
import { initRateState, resetRates } from '../../apps/pce-memory/src/store/rate';

const REPO_ROOT = process.cwd();
const RESULTS_DIR = path.join(REPO_ROOT, 'validation/llm-entity/results');
const RESULTS_JSON_PATH = path.join(RESULTS_DIR, 'results.json');
const REPORT_PATH = path.join(RESULTS_DIR, 'report.md');
const ALLOW_TAGS = ['answer:task'];
const BASE_TIME = Date.parse('2026-03-25T00:00:00.000Z');
const LATENCY_TARGET_MS = 3_000;
const GENERIC_RELATION_TYPES = new Set(['CO_OCCURS', 'RELATES_TO', 'ASSOCIATED_WITH']);

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

type ExpectedGroup = readonly string[];
type QueryTopicId =
  | 'authentication'
  | 'retrieval'
  | 'policy'
  | 'synchronization'
  | 'caching';

type GoldEntity = {
  name: string;
  canonical_key: string;
  type: EntityInput['type'];
  aliases: ExpectedGroup;
};

type GoldRelation = {
  src: string;
  dst: string;
};

type ClaimSpec = {
  id: string;
  topic: QueryTopicId;
  text: string;
  expected_entities: readonly GoldEntity[];
  expected_relations: readonly GoldRelation[];
};

type QueryTopic = {
  id: QueryTopicId;
  label: string;
  query: string;
  manual_seed: GoldEntity;
  claim_ids: readonly string[];
};

type OllamaRuntime = {
  endpoint: string;
  model: string;
};

type ExtractedEntityRecord = {
  name: string;
  canonical_key: string;
  type: string;
};

type ExtractedRelationRecord = {
  src: string;
  dst: string;
  type: string;
};

type ClaimExtractionSnapshot = {
  claim_id: string;
  text: string;
  entities: ExtractedEntityRecord[];
  relations: ExtractedRelationRecord[];
  latency_ms?: number;
};

type ClaimExtractionMetric = {
  claim_id: string;
  extracted_entities: string[];
  expected_entities: string[];
  missing_entities: string[];
  matched_entities: number;
  noise_entities: number;
  precision: number;
  recall: number;
};

type ExtractionQualityMetric = {
  extractor: 'pattern-nlp' | 'llm';
  total_entities: number;
  matched_entities: number;
  noise_entities: number;
  expected_entities: number;
  matched_expected_entities: number;
  precision: number;
  recall: number;
  per_claim: ClaimExtractionMetric[];
};

type NoiseClaimMetric = {
  claim_id: string;
  total_entities: number;
  noise_entities: number;
  noise_rate: number;
};

type NoiseRateMetric = {
  extractor: 'pattern-nlp' | 'llm';
  total_entities: number;
  noise_entities: number;
  noise_rate: number;
  target_lt_0_2: boolean;
  per_claim: NoiseClaimMetric[];
};

type ClaimRelationMetric = {
  claim_id: string;
  extracted_relations: number;
  expected_relations: number;
  matched_relations: number;
  precision: number;
  recall: number;
  meaningful_relations: number;
  generic_relations: number;
  relation_types: Record<string, number>;
};

type RelationQualityMetric = {
  extractor: 'pattern-nlp' | 'llm';
  total_relations: number;
  expected_relations: number;
  matched_relations: number;
  precision: number;
  recall: number;
  meaningful_relations: number;
  generic_relations: number;
  meaningful_rate: number;
  relation_types: Record<string, number>;
  per_claim: ClaimRelationMetric[];
};

type QueryMetric = {
  query: string;
  label: string;
  hits: number;
  relevant_pool: number;
  p_at_3: number;
  top_claim_texts: string[];
};

type QueryExpansionImpact = {
  average_p_at_3: {
    no_entities: number;
    llm_entities: number;
    manual_entities: number;
  };
  queries: Array<{
    query: string;
    label: string;
    no_entities: QueryMetric;
    llm_entities: QueryMetric;
    manual_entities: QueryMetric;
  }>;
  notes: string[];
};

type LatencyMetric = {
  target_ms: number;
  average_ms: number;
  p50_ms: number;
  p95_ms: number;
  max_ms: number;
  over_target_claims: string[];
  meets_target: boolean;
  per_claim: Array<{
    claim_id: string;
    latency_ms: number;
  }>;
};

type ValidationResults = {
  generated_at: string;
  environment: {
    cwd: string;
    node: string;
    ollama_endpoint: string;
    ollama_model: string;
  };
  assumptions: string[];
  dataset: Array<{
    claim_id: string;
    topic: string;
    text: string;
    expected_entities: string[];
    expected_relations: string[];
  }>;
  tests: {
    extraction_quality: {
      pattern: ExtractionQualityMetric;
      llm: ExtractionQualityMetric;
      delta_precision: number;
      delta_recall: number;
    };
    noise_rate: {
      pattern: NoiseRateMetric;
      llm: NoiseRateMetric;
      llm_better_than_pattern: boolean;
    };
    relation_quality: {
      pattern: RelationQualityMetric;
      llm: RelationQualityMetric;
      llm_has_meaningful_relations: boolean;
      notes: string[];
    };
    query_expansion_impact: QueryExpansionImpact;
    latency: LatencyMetric;
  };
  raw_outputs: {
    pattern: ClaimExtractionSnapshot[];
    llm: ClaimExtractionSnapshot[];
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
    const expectedSquashed = squashMatchKey(candidate);
    return (
      normalized === expected ||
      squashed === expectedSquashed ||
      (normalized.length >= 4 &&
        expected.length >= 4 &&
        (normalized.includes(expected) || expected.includes(normalized))) ||
      (squashed.length >= 4 &&
        expectedSquashed.length >= 4 &&
        (squashed.includes(expectedSquashed) || expectedSquashed.includes(squashed)))
    );
  });
}

function uniqueStrings(values: readonly string[]): string[] {
  return [...new Set(values)];
}

function round(value: number, digits: number = 3): number {
  return Number(value.toFixed(digits));
}

function average(values: readonly number[]): number {
  if (values.length === 0) {
    return 0;
  }
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

function mergeHistogram(into: Record<string, number>, from: Record<string, number>): void {
  for (const [key, value] of Object.entries(from)) {
    into[key] = (into[key] ?? 0) + value;
  }
}

function incrementHistogram(histogram: Record<string, number>, key: string): void {
  histogram[key] = (histogram[key] ?? 0) + 1;
}

function pairKey(left: string, right: string): string {
  return [normalizeMatchKey(left), normalizeMatchKey(right)].sort().join('::');
}

function buildPolicyYaml(options: {
  queryExpansionEnabled: boolean;
  maxSeedEntities?: number;
  maxRelatedEntities?: number;
  maxExpansionTerms?: number;
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
      llm_enabled: false,
    },
  });
}

async function setupIsolatedStore(queryExpansionEnabled: boolean): Promise<void> {
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
      yaml: buildPolicyYaml({ queryExpansionEnabled }),
    })
  );
}

function buildProvenance(index: number) {
  return {
    at: new Date(BASE_TIME + index * 60_000).toISOString(),
    actor: 'codex',
    note: 'llm entity validation',
  };
}

async function upsertProjectClaim(text: string, index: number): Promise<string> {
  const upserted = expectSuccess<UpsertPayload>(
    await handleUpsert({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: buildProvenance(index),
    })
  );
  return upserted.id;
}

async function activateTopClaims(query: string, topK: number = 3): Promise<ActivatePayload['claims']> {
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

function goldEntity(
  name: string,
  canonicalKey: string,
  type: EntityInput['type'],
  aliases: string[]
): GoldEntity {
  return {
    name,
    canonical_key: canonicalKey,
    type,
    aliases: uniqueStrings([canonicalKey, ...aliases]),
  };
}

const CLAIMS: readonly ClaimSpec[] = [
  {
    id: 'claim_1',
    topic: 'authentication',
    text: 'JWT rotation protects access tokens during mobile sign-in recovery using RS256',
    expected_entities: [
      goldEntity('JWT', 'jwt', 'Artifact', ['json-web-token']),
      goldEntity('Access Tokens', 'access-token', 'Concept', [
        'access-tokens',
        'access token',
        'access tokens',
      ]),
      goldEntity('Mobile Sign-In Recovery', 'mobile-sign-in-recovery', 'Concept', [
        'sign-in-recovery',
        'mobile sign-in recovery',
      ]),
      goldEntity('RS256', 'rs256', 'Artifact', []),
    ],
    expected_relations: [
      { src: 'jwt', dst: 'access-token' },
      { src: 'jwt', dst: 'rs256' },
    ],
  },
  {
    id: 'claim_2',
    topic: 'retrieval',
    text: 'DuckDB hybrid search uses cosine similarity with HNSW indexing for vector retrieval',
    expected_entities: [
      goldEntity('DuckDB', 'duckdb', 'Artifact', []),
      goldEntity('Hybrid Search', 'hybrid-search', 'Concept', ['hybrid search']),
      goldEntity('Cosine Similarity', 'cosine-similarity', 'Concept', ['cosine similarity']),
      goldEntity('HNSW Indexing', 'hnsw', 'Artifact', ['hnsw-indexing', 'hnsw indexing']),
      goldEntity('Vector Retrieval', 'vector-retrieval', 'Concept', ['vector retrieval']),
    ],
    expected_relations: [
      { src: 'hybrid-search', dst: 'duckdb' },
      { src: 'hybrid-search', dst: 'cosine-similarity' },
      { src: 'hybrid-search', dst: 'hnsw' },
      { src: 'hnsw', dst: 'vector-retrieval' },
    ],
  },
  {
    id: 'claim_3',
    topic: 'policy',
    text: 'The pce_memory_activate handler validates scope and boundary before ranking',
    expected_entities: [
      goldEntity('pce_memory_activate', 'pce-memory-activate', 'Artifact', [
        'pce_memory_activate',
        'pce-memory-activate-handler',
      ]),
      goldEntity('Scope', 'scope', 'Concept', []),
      goldEntity('Boundary', 'boundary', 'Concept', []),
      goldEntity('Ranking', 'ranking', 'Concept', []),
    ],
    expected_relations: [
      { src: 'pce-memory-activate', dst: 'scope' },
      { src: 'pce-memory-activate', dst: 'boundary' },
      { src: 'pce-memory-activate', dst: 'ranking' },
    ],
  },
  {
    id: 'claim_4',
    topic: 'synchronization',
    text: 'Git-based CRDT sync merges claims by content_hash with monotonic boundary upgrade',
    expected_entities: [
      goldEntity('Git-based CRDT Sync', 'crdt-sync', 'Concept', [
        'git-based-crdt-sync',
        'git based crdt sync',
        'sync',
      ]),
      goldEntity('Claims', 'claims', 'Concept', []),
      goldEntity('content_hash', 'content-hash', 'Concept', ['content_hash', 'content hash']),
      goldEntity('Boundary Upgrade', 'boundary-upgrade', 'Concept', [
        'monotonic-boundary-upgrade',
        'boundary upgrade',
      ]),
    ],
    expected_relations: [
      { src: 'crdt-sync', dst: 'claims' },
      { src: 'crdt-sync', dst: 'content-hash' },
      { src: 'crdt-sync', dst: 'boundary-upgrade' },
    ],
  },
  {
    id: 'claim_5',
    topic: 'caching',
    text: 'Redis cache stores rendered dashboard fragments with TTL-based eviction',
    expected_entities: [
      goldEntity('Redis', 'redis', 'Artifact', []),
      goldEntity('Cache', 'cache', 'Concept', ['redis-cache']),
      goldEntity('Dashboard Fragments', 'dashboard-fragments', 'Concept', [
        'rendered-dashboard-fragments',
        'dashboard fragments',
      ]),
      goldEntity('TTL-based Eviction', 'ttl-based-eviction', 'Concept', [
        'ttl eviction',
        'ttl-based eviction',
      ]),
    ],
    expected_relations: [
      { src: 'redis', dst: 'cache' },
      { src: 'cache', dst: 'dashboard-fragments' },
      { src: 'cache', dst: 'ttl-based-eviction' },
    ],
  },
  {
    id: 'claim_6',
    topic: 'authentication',
    text: 'OAuth device flow pins PKCE verifier state before token exchange with rotating refresh grants',
    expected_entities: [
      goldEntity('OAuth Device Flow', 'oauth-device-flow', 'Concept', [
        'oauth device flow',
      ]),
      goldEntity('PKCE', 'pkce', 'Artifact', []),
      goldEntity('Verifier State', 'verifier-state', 'Concept', ['verifier state']),
      goldEntity('Token Exchange', 'token-exchange', 'Concept', ['token exchange']),
      goldEntity('Refresh Grants', 'refresh-grants', 'Concept', ['refresh grants']),
    ],
    expected_relations: [
      { src: 'oauth-device-flow', dst: 'pkce' },
      { src: 'oauth-device-flow', dst: 'token-exchange' },
      { src: 'token-exchange', dst: 'refresh-grants' },
    ],
  },
  {
    id: 'claim_7',
    topic: 'retrieval',
    text: 'pgvector semantic search blends BM25 reranking with approximate nearest-neighbor recall',
    expected_entities: [
      goldEntity('pgvector', 'pgvector', 'Artifact', []),
      goldEntity('Semantic Search', 'semantic-search', 'Concept', ['semantic search']),
      goldEntity('BM25', 'bm25', 'Artifact', []),
      goldEntity('Reranking', 'reranking', 'Concept', ['rerank']),
      goldEntity(
        'Approximate Nearest-Neighbor Recall',
        'ann-recall',
        'Concept',
        ['approximate-nearest-neighbor-recall', 'nearest-neighbor-recall', 'ann recall']
      ),
    ],
    expected_relations: [
      { src: 'semantic-search', dst: 'pgvector' },
      { src: 'semantic-search', dst: 'bm25' },
      { src: 'semantic-search', dst: 'ann-recall' },
    ],
  },
  {
    id: 'claim_8',
    topic: 'policy',
    text: 'SchemaDriftGuard blocks tenant rollout when policy-bound migration steps violate boundary rules',
    expected_entities: [
      goldEntity('SchemaDriftGuard', 'schemadriftguard', 'Artifact', [
        'schema-drift-guard',
      ]),
      goldEntity('Tenant Rollout', 'tenant-rollout', 'Concept', ['tenant rollout']),
      goldEntity('Policy-bound Migration Steps', 'policy-bound-migration', 'Concept', [
        'policy-bound-migration-steps',
        'migration-steps',
        'policy bound migration steps',
      ]),
      goldEntity('Boundary Rules', 'boundary-rules', 'Concept', ['boundary rules']),
    ],
    expected_relations: [
      { src: 'schemadriftguard', dst: 'tenant-rollout' },
      { src: 'schemadriftguard', dst: 'policy-bound-migration' },
      { src: 'policy-bound-migration', dst: 'boundary-rules' },
    ],
  },
  {
    id: 'claim_9',
    topic: 'synchronization',
    text: 'Replica repair replays vector clocks before gossip-based conflict resolution in offline sync',
    expected_entities: [
      goldEntity('Replica Repair', 'replica-repair', 'Concept', ['replica repair']),
      goldEntity('Vector Clocks', 'vector-clocks', 'Concept', [
        'vector clocks',
        'vector-clock',
      ]),
      goldEntity('Conflict Resolution', 'conflict-resolution', 'Concept', [
        'gossip-based-conflict-resolution',
        'conflict resolution',
      ]),
      goldEntity('Offline Sync', 'offline-sync', 'Concept', ['offline sync']),
    ],
    expected_relations: [
      { src: 'replica-repair', dst: 'vector-clocks' },
      { src: 'replica-repair', dst: 'conflict-resolution' },
      { src: 'offline-sync', dst: 'conflict-resolution' },
    ],
  },
  {
    id: 'claim_10',
    topic: 'caching',
    text: 'CDN edge cache invalidates persisted GraphQL responses after shard rebalancing',
    expected_entities: [
      goldEntity('CDN Edge Cache', 'cdn-edge-cache', 'Artifact', [
        'edge-cache',
        'cdn cache',
      ]),
      goldEntity(
        'Persisted GraphQL Responses',
        'persisted-graphql-responses',
        'Concept',
        ['graphql responses', 'persisted query responses']
      ),
      goldEntity('Shard Rebalancing', 'shard-rebalancing', 'Concept', ['shard rebalancing']),
    ],
    expected_relations: [
      { src: 'cdn-edge-cache', dst: 'persisted-graphql-responses' },
      { src: 'cdn-edge-cache', dst: 'shard-rebalancing' },
    ],
  },
];

const QUERY_TOPICS: readonly QueryTopic[] = [
  {
    id: 'authentication',
    label: 'Authentication',
    query: 'authentication',
    manual_seed: goldEntity('Authentication', 'authentication', 'Concept', []),
    claim_ids: ['claim_1', 'claim_6'],
  },
  {
    id: 'retrieval',
    label: 'Retrieval',
    query: 'retrieval',
    manual_seed: goldEntity('Retrieval', 'retrieval', 'Concept', []),
    claim_ids: ['claim_2', 'claim_7'],
  },
  {
    id: 'policy',
    label: 'Policy',
    query: 'policy',
    manual_seed: goldEntity('Policy', 'policy', 'Concept', []),
    claim_ids: ['claim_3', 'claim_8'],
  },
  {
    id: 'synchronization',
    label: 'Synchronization',
    query: 'synchronization',
    manual_seed: goldEntity('Synchronization', 'synchronization', 'Concept', []),
    claim_ids: ['claim_4', 'claim_9'],
  },
  {
    id: 'caching',
    label: 'Caching',
    query: 'caching',
    manual_seed: goldEntity('Caching', 'caching', 'Concept', []),
    claim_ids: ['claim_5', 'claim_10'],
  },
];

function snapshotFromPatternExtractor(claim: ClaimSpec): ClaimExtractionSnapshot {
  const entities = extractEntities(claim.text).map((entity) => ({
    name: entity.name,
    canonical_key: entity.canonical_key,
    type: entity.graph_type,
  }));

  const relations: ExtractedRelationRecord[] = [];
  for (let index = 0; index < entities.length; index++) {
    for (let otherIndex = index + 1; otherIndex < entities.length; otherIndex++) {
      relations.push({
        src: entities[index]!.canonical_key,
        dst: entities[otherIndex]!.canonical_key,
        type: 'CO_OCCURS',
      });
    }
  }

  return {
    claim_id: claim.id,
    text: claim.text,
    entities,
    relations,
  };
}

async function snapshotFromLlmExtractor(
  claim: ClaimSpec,
  runtime: OllamaRuntime
): Promise<ClaimExtractionSnapshot> {
  const startedAt = performance.now();
  const extracted = await extractEntitiesWithLLM(claim.text, {
    ollamaEndpoint: runtime.endpoint,
    model: runtime.model,
  });
  const latencyMs = performance.now() - startedAt;

  return {
    claim_id: claim.id,
    text: claim.text,
    latency_ms: round(latencyMs),
    entities: extracted.entities.map((entity: LlmEntityCandidate) => ({
      name: entity.name,
      canonical_key: entity.canonical_key,
      type: entity.type,
    })),
    relations: extracted.relations.map((relation: LlmRelationCandidate) => ({
      src: relation.src,
      dst: relation.dst,
      type: relation.type,
    })),
  };
}

function resolveExpectedEntity(value: string, claim: ClaimSpec): GoldEntity | undefined {
  return claim.expected_entities.find((entity) => matchesExpectedGroup(value, entity.aliases));
}

function evaluateExtractionQuality(
  claims: readonly ClaimSpec[],
  snapshots: readonly ClaimExtractionSnapshot[],
  extractor: 'pattern-nlp' | 'llm'
): ExtractionQualityMetric {
  let totalEntities = 0;
  let matchedEntities = 0;
  let noiseEntities = 0;
  let expectedEntities = 0;
  let matchedExpectedEntities = 0;
  const perClaim: ClaimExtractionMetric[] = [];

  for (const claim of claims) {
    const snapshot = snapshots.find((item) => item.claim_id === claim.id);
    const extractedKeys = uniqueStrings(snapshot?.entities.map((entity) => entity.canonical_key) ?? []);
    const matchedExpected = new Set<string>();
    let claimMatchedEntities = 0;
    let claimNoiseEntities = 0;

    for (const key of extractedKeys) {
      const expected = resolveExpectedEntity(key, claim);
      if (expected) {
        claimMatchedEntities++;
        matchedExpected.add(expected.canonical_key);
      } else {
        claimNoiseEntities++;
      }
    }

    const expectedKeys = claim.expected_entities.map((entity) => entity.canonical_key);
    const missingEntities = expectedKeys.filter((key) => !matchedExpected.has(key));

    totalEntities += extractedKeys.length;
    matchedEntities += claimMatchedEntities;
    noiseEntities += claimNoiseEntities;
    expectedEntities += expectedKeys.length;
    matchedExpectedEntities += matchedExpected.size;

    perClaim.push({
      claim_id: claim.id,
      extracted_entities: extractedKeys,
      expected_entities: expectedKeys,
      missing_entities: missingEntities,
      matched_entities: claimMatchedEntities,
      noise_entities: claimNoiseEntities,
      precision: round(extractedKeys.length === 0 ? 0 : claimMatchedEntities / extractedKeys.length),
      recall: round(expectedKeys.length === 0 ? 0 : matchedExpected.size / expectedKeys.length),
    });
  }

  return {
    extractor,
    total_entities: totalEntities,
    matched_entities: matchedEntities,
    noise_entities: noiseEntities,
    expected_entities: expectedEntities,
    matched_expected_entities: matchedExpectedEntities,
    precision: round(totalEntities === 0 ? 0 : matchedEntities / totalEntities),
    recall: round(expectedEntities === 0 ? 0 : matchedExpectedEntities / expectedEntities),
    per_claim: perClaim,
  };
}

function buildNoiseRateMetric(
  claims: readonly ClaimSpec[],
  snapshots: readonly ClaimExtractionSnapshot[],
  extractor: 'pattern-nlp' | 'llm'
): NoiseRateMetric {
  const perClaim: NoiseClaimMetric[] = [];
  let totalEntities = 0;
  let noiseEntities = 0;

  for (const claim of claims) {
    const snapshot = snapshots.find((item) => item.claim_id === claim.id);
    const extractedKeys = uniqueStrings(snapshot?.entities.map((entity) => entity.canonical_key) ?? []);
    let claimNoise = 0;

    for (const key of extractedKeys) {
      if (!resolveExpectedEntity(key, claim)) {
        claimNoise++;
      }
    }

    totalEntities += extractedKeys.length;
    noiseEntities += claimNoise;
    perClaim.push({
      claim_id: claim.id,
      total_entities: extractedKeys.length,
      noise_entities: claimNoise,
      noise_rate: round(extractedKeys.length === 0 ? 0 : claimNoise / extractedKeys.length),
    });
  }

  const noiseRate = totalEntities === 0 ? 0 : noiseEntities / totalEntities;
  return {
    extractor,
    total_entities: totalEntities,
    noise_entities: noiseEntities,
    noise_rate: round(noiseRate),
    target_lt_0_2: noiseRate < 0.2,
    per_claim: perClaim,
  };
}

function buildRelationQualityMetric(
  claims: readonly ClaimSpec[],
  snapshots: readonly ClaimExtractionSnapshot[],
  extractor: 'pattern-nlp' | 'llm'
): RelationQualityMetric {
  let totalRelations = 0;
  let expectedRelations = 0;
  let matchedRelations = 0;
  let meaningfulRelations = 0;
  let genericRelations = 0;
  const relationTypes: Record<string, number> = {};
  const perClaim: ClaimRelationMetric[] = [];

  for (const claim of claims) {
    const snapshot = snapshots.find((item) => item.claim_id === claim.id);
    const extractedRelations = snapshot?.relations ?? [];
    const expectedPairKeys = new Set(
      claim.expected_relations.map((relation) => pairKey(relation.src, relation.dst))
    );
    const matchedPairs = new Set<string>();
    const claimRelationTypes: Record<string, number> = {};
    let claimMeaningful = 0;
    let claimGeneric = 0;

    for (const relation of extractedRelations) {
      const src = resolveExpectedEntity(relation.src, claim);
      const dst = resolveExpectedEntity(relation.dst, claim);
      const type = relation.type.toUpperCase();

      incrementHistogram(claimRelationTypes, type);
      incrementHistogram(relationTypes, type);

      if (GENERIC_RELATION_TYPES.has(type)) {
        claimGeneric++;
      } else {
        claimMeaningful++;
      }

      if (src && dst) {
        const key = pairKey(src.canonical_key, dst.canonical_key);
        if (expectedPairKeys.has(key)) {
          matchedPairs.add(key);
        }
      }
    }

    totalRelations += extractedRelations.length;
    expectedRelations += expectedPairKeys.size;
    matchedRelations += matchedPairs.size;
    meaningfulRelations += claimMeaningful;
    genericRelations += claimGeneric;

    perClaim.push({
      claim_id: claim.id,
      extracted_relations: extractedRelations.length,
      expected_relations: expectedPairKeys.size,
      matched_relations: matchedPairs.size,
      precision: round(extractedRelations.length === 0 ? 0 : matchedPairs.size / extractedRelations.length),
      recall: round(expectedPairKeys.size === 0 ? 0 : matchedPairs.size / expectedPairKeys.size),
      meaningful_relations: claimMeaningful,
      generic_relations: claimGeneric,
      relation_types: claimRelationTypes,
    });
  }

  return {
    extractor,
    total_relations: totalRelations,
    expected_relations: expectedRelations,
    matched_relations: matchedRelations,
    precision: round(totalRelations === 0 ? 0 : matchedRelations / totalRelations),
    recall: round(expectedRelations === 0 ? 0 : matchedRelations / expectedRelations),
    meaningful_relations: meaningfulRelations,
    generic_relations: genericRelations,
    meaningful_rate: round(totalRelations === 0 ? 0 : meaningfulRelations / totalRelations),
    relation_types: relationTypes,
    per_claim: perClaim,
  };
}

async function resolveOllamaRuntime(): Promise<OllamaRuntime | null> {
  const endpoint = process.env['PCE_TEST_OLLAMA_ENDPOINT'] ?? 'http://127.0.0.1:11434';
  const preferredModel = process.env['PCE_TEST_OLLAMA_MODEL'] ?? 'qwen3.5:9b';
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
      model: modelIds.includes(preferredModel) ? preferredModel : modelIds[0]!,
    };
  } catch {
    return null;
  } finally {
    clearTimeout(timeout);
  }
}

function buildGeneratedEntityId(type: EntityInput['type'], canonicalKey: string): string {
  return `ent_${computeContentHash(`entity:${type}:${canonicalKey}`).slice(0, 16)}`;
}

function buildGeneratedRelationId(type: string, srcId: string, dstId: string): string {
  return `rel_${computeContentHash(`relation:${type}:${srcId}:${dstId}`).slice(0, 16)}`;
}

async function materializeGraphForClaim(
  claimId: string,
  entities: readonly GoldEntity[] | readonly ExtractedEntityRecord[],
  relations: readonly GoldRelation[] | readonly ExtractedRelationRecord[],
  extractor: 'manual' | 'llm'
): Promise<void> {
  const entityIdsByKey = new Map<string, string>();
  const dedupedEntities = new Map<string, EntityInput>();

  for (const entity of entities) {
    const canonicalKey = entity.canonical_key;
    if (!canonicalKey) {
      continue;
    }

    const existing = await findEntityByCanonicalKey(canonicalKey);
    const entityId = existing?.id ?? buildGeneratedEntityId(entity.type as EntityInput['type'], canonicalKey);
    entityIdsByKey.set(canonicalKey, entityId);
    dedupedEntities.set(entityId, {
      id: entityId,
      type: entity.type as EntityInput['type'],
      name: entity.name,
      canonical_key: canonicalKey,
      attrs: {
        extractor,
      },
    });
  }

  for (const entity of dedupedEntities.values()) {
    await upsertEntity(entity);
    await linkClaimEntity(claimId, entity.id);
  }

  const seenRelations = new Set<string>();
  for (const relation of relations) {
    const srcId = entityIdsByKey.get(relation.src);
    const dstId = entityIdsByKey.get(relation.dst);
    if (!srcId || !dstId || srcId === dstId) {
      continue;
    }

    const relationType = 'type' in relation ? relation.type.toUpperCase() : 'RELATES_TO';
    const relationId = buildGeneratedRelationId(relationType, srcId, dstId);
    if (seenRelations.has(relationId)) {
      continue;
    }
    seenRelations.add(relationId);
    await upsertRelation({
      id: relationId,
      src_id: srcId,
      dst_id: dstId,
      type: relationType,
      evidence_claim_id: claimId,
      props: {
        extractor,
      },
    });
  }
}

function manualEntitiesForClaim(claim: ClaimSpec): GoldEntity[] {
  const topic = QUERY_TOPICS.find((item) => item.id === claim.topic);
  return topic ? [...claim.expected_entities, topic.manual_seed] : [...claim.expected_entities];
}

async function seedScenario(
  scenario: 'no_entities' | 'llm_entities' | 'manual_entities',
  llmSnapshots: readonly ClaimExtractionSnapshot[]
): Promise<QueryMetric[]> {
  await setupIsolatedStore(true);
  const claimIdsBySpecId = new Map<string, string>();
  const claimTextsById = new Map<string, string>();

  for (let index = 0; index < CLAIMS.length; index++) {
    const claim = CLAIMS[index]!;
    const claimId = await upsertProjectClaim(claim.text, index);
    claimIdsBySpecId.set(claim.id, claimId);
    claimTextsById.set(claimId, claim.text);

    if (scenario === 'manual_entities') {
      await materializeGraphForClaim(claimId, manualEntitiesForClaim(claim), [], 'manual');
      continue;
    }

    if (scenario === 'llm_entities') {
      const snapshot = llmSnapshots.find((item) => item.claim_id === claim.id);
      if (snapshot) {
        await materializeGraphForClaim(claimId, snapshot.entities, snapshot.relations, 'llm');
      }
    }
  }

  const metrics: QueryMetric[] = [];
  for (const topic of QUERY_TOPICS) {
    const claims = await activateTopClaims(topic.query, 3);
    const ids = claims.map((entry) => entry.claim.id);
    const relevantIds = new Set(topic.claim_ids.map((claimId) => claimIdsBySpecId.get(claimId)!));
    metrics.push({
      query: topic.query,
      label: topic.label,
      hits: ids.filter((id) => relevantIds.has(id)).length,
      relevant_pool: relevantIds.size,
      p_at_3: round(precisionAtK(ids, relevantIds, 3)),
      top_claim_texts: ids.map((id) => claimTextsById.get(id) ?? id),
    });
  }

  return metrics;
}

function buildLatencyMetric(llmSnapshots: readonly ClaimExtractionSnapshot[]): LatencyMetric {
  const perClaim = llmSnapshots.map((snapshot) => ({
    claim_id: snapshot.claim_id,
    latency_ms: snapshot.latency_ms ?? 0,
  }));
  const values = perClaim.map((item) => item.latency_ms);
  const overTargetClaims = perClaim
    .filter((item) => item.latency_ms > LATENCY_TARGET_MS)
    .map((item) => item.claim_id);

  return {
    target_ms: LATENCY_TARGET_MS,
    average_ms: round(average(values)),
    p50_ms: round(percentile(values, 0.5)),
    p95_ms: round(percentile(values, 0.95)),
    max_ms: round(Math.max(...values, 0)),
    over_target_claims: overTargetClaims,
    meets_target: overTargetClaims.length === 0,
    per_claim: perClaim,
  };
}

function renderHistogram(histogram: Record<string, number>): string {
  const entries = Object.entries(histogram).sort((left, right) => right[1] - left[1]);
  return entries.length === 0 ? 'none' : entries.map(([key, value]) => `${key}: ${value}`).join(', ');
}

function buildReport(results: ValidationResults): string {
  const queryRows = results.tests.query_expansion_impact.queries
    .map(
      (metric) =>
        `| ${metric.label} | ${metric.no_entities.p_at_3} | ${metric.llm_entities.p_at_3} | ${metric.manual_entities.p_at_3} | ${metric.llm_entities.hits}/${metric.llm_entities.relevant_pool} |`
    )
    .join('\n');

  return [
    '# LLM Entity Extraction Validation Report',
    '',
    `Generated at: ${results.generated_at}`,
    '',
    `Runtime: ${results.environment.ollama_model} @ ${results.environment.ollama_endpoint}`,
    '',
    '## Assumptions',
    '',
    ...results.assumptions.map((item) => `- ${item}`),
    '',
    '## Test 1: Extraction Quality',
    '',
    '| Extractor | Total entities | Matched | Noise | Precision | Recall |',
    '| --- | ---: | ---: | ---: | ---: | ---: |',
    `| Pattern NLP | ${results.tests.extraction_quality.pattern.total_entities} | ${results.tests.extraction_quality.pattern.matched_entities} | ${results.tests.extraction_quality.pattern.noise_entities} | ${results.tests.extraction_quality.pattern.precision} | ${results.tests.extraction_quality.pattern.recall} |`,
    `| LLM | ${results.tests.extraction_quality.llm.total_entities} | ${results.tests.extraction_quality.llm.matched_entities} | ${results.tests.extraction_quality.llm.noise_entities} | ${results.tests.extraction_quality.llm.precision} | ${results.tests.extraction_quality.llm.recall} |`,
    '',
    `Precision delta (LLM - Pattern): ${results.tests.extraction_quality.delta_precision}`,
    '',
    `Recall delta (LLM - Pattern): ${results.tests.extraction_quality.delta_recall}`,
    '',
    '## Test 2: Noise Rate',
    '',
    '| Extractor | Noise entities | Total entities | Noise rate | Target < 0.2 |',
    '| --- | ---: | ---: | ---: | --- |',
    `| Pattern NLP | ${results.tests.noise_rate.pattern.noise_entities} | ${results.tests.noise_rate.pattern.total_entities} | ${results.tests.noise_rate.pattern.noise_rate} | ${results.tests.noise_rate.pattern.target_lt_0_2} |`,
    `| LLM | ${results.tests.noise_rate.llm.noise_entities} | ${results.tests.noise_rate.llm.total_entities} | ${results.tests.noise_rate.llm.noise_rate} | ${results.tests.noise_rate.llm.target_lt_0_2} |`,
    '',
    `LLM better than pattern: ${results.tests.noise_rate.llm_better_than_pattern}`,
    '',
    '## Test 3: Relation Quality',
    '',
    '| Extractor | Total relations | Matched pairs | Precision | Recall | Meaningful relations | Meaningful rate |',
    '| --- | ---: | ---: | ---: | ---: | ---: | ---: |',
    `| Pattern NLP | ${results.tests.relation_quality.pattern.total_relations} | ${results.tests.relation_quality.pattern.matched_relations} | ${results.tests.relation_quality.pattern.precision} | ${results.tests.relation_quality.pattern.recall} | ${results.tests.relation_quality.pattern.meaningful_relations} | ${results.tests.relation_quality.pattern.meaningful_rate} |`,
    `| LLM | ${results.tests.relation_quality.llm.total_relations} | ${results.tests.relation_quality.llm.matched_relations} | ${results.tests.relation_quality.llm.precision} | ${results.tests.relation_quality.llm.recall} | ${results.tests.relation_quality.llm.meaningful_relations} | ${results.tests.relation_quality.llm.meaningful_rate} |`,
    '',
    `Pattern relation types: ${renderHistogram(results.tests.relation_quality.pattern.relation_types)}`,
    '',
    `LLM relation types: ${renderHistogram(results.tests.relation_quality.llm.relation_types)}`,
    '',
    `LLM has meaningful relations: ${results.tests.relation_quality.llm_has_meaningful_relations}`,
    '',
    ...results.tests.relation_quality.notes.map((note) => `- ${note}`),
    '',
    '## Test 4: Query Expansion Impact',
    '',
    '| Query | P@3 No Entities | P@3 LLM Entities | P@3 Manual Entities | LLM Hits |',
    '| --- | ---: | ---: | ---: | ---: |',
    queryRows,
    '',
    `Average P@3 without entities: ${results.tests.query_expansion_impact.average_p_at_3.no_entities}`,
    '',
    `Average P@3 with LLM entities: ${results.tests.query_expansion_impact.average_p_at_3.llm_entities}`,
    '',
    `Average P@3 with manual entities: ${results.tests.query_expansion_impact.average_p_at_3.manual_entities}`,
    '',
    ...results.tests.query_expansion_impact.notes.map((note) => `- ${note}`),
    '',
    '## Test 5: Latency',
    '',
    `Target per claim: < ${results.tests.latency.target_ms}ms`,
    '',
    `Average: ${results.tests.latency.average_ms}ms`,
    '',
    `P50: ${results.tests.latency.p50_ms}ms`,
    '',
    `P95: ${results.tests.latency.p95_ms}ms`,
    '',
    `Max: ${results.tests.latency.max_ms}ms`,
    '',
    `Meets target: ${results.tests.latency.meets_target}`,
    '',
    `Over-target claims: ${results.tests.latency.over_target_claims.join(', ') || 'none'}`,
    '',
  ].join('\n');
}

async function writeResults(results: ValidationResults): Promise<void> {
  await fs.mkdir(RESULTS_DIR, { recursive: true });
  await fs.writeFile(RESULTS_JSON_PATH, `${JSON.stringify(results, null, 2)}\n`, 'utf8');
  await fs.writeFile(REPORT_PATH, buildReport(results), 'utf8');
}

async function main(): Promise<void> {
  const runtime = await resolveOllamaRuntime();
  if (!runtime) {
    throw new Error('Ollama was not reachable at http://127.0.0.1:11434/v1/models within 1.5s.');
  }

  const patternSnapshots = CLAIMS.map((claim) => snapshotFromPatternExtractor(claim));
  const llmSnapshots: ClaimExtractionSnapshot[] = [];
  for (const claim of CLAIMS) {
    llmSnapshots.push(await snapshotFromLlmExtractor(claim, runtime));
  }

  const extractionPattern = evaluateExtractionQuality(CLAIMS, patternSnapshots, 'pattern-nlp');
  const extractionLlm = evaluateExtractionQuality(CLAIMS, llmSnapshots, 'llm');

  const noisePattern = buildNoiseRateMetric(CLAIMS, patternSnapshots, 'pattern-nlp');
  const noiseLlm = buildNoiseRateMetric(CLAIMS, llmSnapshots, 'llm');

  const relationPattern = buildRelationQualityMetric(CLAIMS, patternSnapshots, 'pattern-nlp');
  const relationLlm = buildRelationQualityMetric(CLAIMS, llmSnapshots, 'llm');

  const noEntityMetrics = await seedScenario('no_entities', llmSnapshots);
  const llmEntityMetrics = await seedScenario('llm_entities', llmSnapshots);
  const manualEntityMetrics = await seedScenario('manual_entities', llmSnapshots);

  const queryExpansionImpact: QueryExpansionImpact = {
    average_p_at_3: {
      no_entities: round(average(noEntityMetrics.map((metric) => metric.p_at_3))),
      llm_entities: round(average(llmEntityMetrics.map((metric) => metric.p_at_3))),
      manual_entities: round(average(manualEntityMetrics.map((metric) => metric.p_at_3))),
    },
    queries: QUERY_TOPICS.map((topic, index) => ({
      query: topic.query,
      label: topic.label,
      no_entities: noEntityMetrics[index]!,
      llm_entities: llmEntityMetrics[index]!,
      manual_entities: manualEntityMetrics[index]!,
    })),
    notes: [
      'The manual-entity arm adds one shared topical seed entity per claim cluster as an oracle upper bound for query expansion.',
      'The LLM arm uses only entities and relations produced by the real Ollama-backed extractor on the claim text itself.',
      'All three retrieval arms reuse the same deterministic local embedding service so score differences come from entity graph coverage, not embedding drift.',
    ],
  };

  const assumptions = [
    'Entity precision/recall uses a manually curated gold set with alias matching so hyphenation and snake_case variants are treated as the same concept.',
    'Relation quality scores unordered meaningful pairs; relation type histograms are reported separately to show whether the LLM emits typed edges instead of only generic co-occurrence.',
    'Query expansion compares three retrieval conditions: no linked entities, only LLM-extracted entities/relations, and an oracle manual-entity upper bound with shared topical seeds.',
  ];

  const results: ValidationResults = {
    generated_at: new Date().toISOString(),
    environment: {
      cwd: REPO_ROOT,
      node: process.version,
      ollama_endpoint: runtime.endpoint,
      ollama_model: runtime.model,
    },
    assumptions,
    dataset: CLAIMS.map((claim) => ({
      claim_id: claim.id,
      topic: claim.topic,
      text: claim.text,
      expected_entities: claim.expected_entities.map((entity) => entity.canonical_key),
      expected_relations: claim.expected_relations.map((relation) => `${relation.src}->${relation.dst}`),
    })),
    tests: {
      extraction_quality: {
        pattern: extractionPattern,
        llm: extractionLlm,
        delta_precision: round(extractionLlm.precision - extractionPattern.precision),
        delta_recall: round(extractionLlm.recall - extractionPattern.recall),
      },
      noise_rate: {
        pattern: noisePattern,
        llm: noiseLlm,
        llm_better_than_pattern: noiseLlm.noise_rate < noisePattern.noise_rate,
      },
      relation_quality: {
        pattern: relationPattern,
        llm: relationLlm,
        llm_has_meaningful_relations: relationLlm.meaningful_relations > 0,
        notes: [
          'Pattern NLP relations are synthetic co-occurs edges between all extracted entities in the same claim.',
          'LLM relation quality improves only when the extractor emits typed edges that land on the gold relation pairs.',
        ],
      },
      query_expansion_impact: queryExpansionImpact,
      latency: buildLatencyMetric(llmSnapshots),
    },
    raw_outputs: {
      pattern: patternSnapshots,
      llm: llmSnapshots,
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

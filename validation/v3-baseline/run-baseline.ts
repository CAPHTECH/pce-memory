#!/usr/bin/env node

import { createHash } from 'node:crypto';
import { promises as fs } from 'node:fs';
import path from 'node:path';

import {
  handleActivate,
  handleObserve,
  handlePolicyApply,
  handleUpsert,
} from '../../apps/pce-memory/src/core/handlers';
import {
  closeDb,
  getConnection,
  initDb,
  initSchema,
  resetDbAsync,
} from '../../apps/pce-memory/src/db/connection';
import { resetLayerScopeState } from '../../apps/pce-memory/src/state/layerScopeState';
import { initMemoryState, resetMemoryState } from '../../apps/pce-memory/src/state/memoryState';
import { setEmbeddingService } from '../../apps/pce-memory/src/store/hybridSearch';
import { initRateState, resetRates } from '../../apps/pce-memory/src/store/rate';

const REPO_ROOT = process.cwd();
const RESULTS_DIR = path.join(REPO_ROOT, 'validation/v3-baseline/results');
const RESULTS_JSON_PATH = path.join(RESULTS_DIR, 'baseline.json');
const REPORT_PATH = path.join(RESULTS_DIR, 'baseline-report.md');
const ALLOW_TAGS = ['answer:task'];
const NOW = new Date();

type EmbeddingService = Parameters<typeof setEmbeddingService>[0];
type ClaimKind = 'fact' | 'preference' | 'task' | 'policy_hint';
type ClaimScope = 'session' | 'project' | 'principle';
type BoundaryClass = 'public' | 'internal' | 'pii';
type MemoryType = 'evidence' | 'working_state' | 'knowledge' | 'procedure' | 'norm';
type ActivateIntent = 'resume_task' | 'policy_check' | 'design_decision' | 'debug_incident';

type ToolResultLike = {
  isError?: boolean;
  structuredContent?: Record<string, unknown>;
  content?: Array<{ type?: string; text?: string }>;
};

type LeftLike = {
  _tag: 'Left';
  left: {
    message: string;
  };
};

type ActivateClaim = {
  claim: {
    id: string;
    text: string;
    kind: string;
    scope: string;
    boundary_class: string;
    memory_type?: string | null;
  };
  score: number;
  rank?: number;
  selection_reason?: string;
};

type ActivatePayload = {
  active_context_id: string;
  claims: ActivateClaim[];
  claims_count: number;
  has_more: boolean;
  intent?: string;
  policy_version: string;
  request_id: string;
  trace_id: string;
  next_cursor?: string;
};

type UpsertPayload = {
  id: string;
  is_new: boolean;
};

type ObservePayload = {
  observation_id: string;
};

type ClaimRecord = {
  id: string;
  text: string;
  created_at: string;
  updated_at: string;
  recency_anchor: string;
};

type BenchmarkCase = {
  label: string;
  query: string;
  expected_id?: string;
  actual_ids: string[];
  success: boolean;
  notes?: string;
};

type BenchmarkResults = {
  generated_at: string;
  environment: {
    repo_root: string;
    node: string;
    database: ':memory:';
    embedding_service: string;
    internal_handlers: true;
  };
  benchmarks: {
    B1: FreshnessResult;
    B2: UsageLearningResult;
    B3: MaintenanceResult;
    B4: ConnectivityResult;
    B5: CombinedResult;
  };
};

type FreshnessResult = {
  name: 'FRESHNESS';
  score: number;
  metric: 'latest_top1_rate';
  expected_baseline: string;
  latest_top1_rate: number;
  latest_pair_win_rate: number;
  tracked_topics: number;
  cases: BenchmarkCase[];
};

type UsageLearningResult = {
  name: 'USAGE_LEARNING';
  score: number;
  metric: 'spearman_frequency_vs_final_rank';
  expected_baseline: string;
  spearman_frequency_vs_final_rank: number;
  final_query: string;
  tracked_claims: Array<{
    id: string;
    label: string;
    retrieval_count: number;
    final_rank: number | null;
  }>;
};

type MaintenanceResult = {
  name: 'MAINTENANCE';
  score: number;
  metric: 'detected_hint_category_ratio';
  expected_baseline: string;
  detected_hint_category_ratio: number;
  detected_categories: string[];
  checked_categories: string[];
  activate_keys: string[];
  response_excerpt: string;
};

type ConnectivityResult = {
  name: 'CONNECTIVITY';
  score: number;
  metric: 'related_claim_recall_at_5';
  expected_baseline: string;
  related_claim_recall_at_5: number;
  pair_count: number;
  cases: BenchmarkCase[];
};

type CombinedResult = {
  name: 'COMBINED';
  score: number;
  metric: 'mean(freshness_pair_accuracy,relevance_precision_at_8)';
  expected_baseline: string;
  freshness_pair_accuracy: number;
  relevance_precision_at_8: number;
  final_query: string;
  final_result_ids: string[];
  expected_relevant_ids: string[];
};

function sha256(input: string): string {
  return `sha256:${createHash('sha256').update(input).digest('hex')}`;
}

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

function isLeft(value: unknown): value is LeftLike {
  return (
    typeof value === 'object' &&
    value !== null &&
    (value as { _tag?: unknown })._tag === 'Left' &&
    typeof (value as LeftLike).left?.message === 'string'
  );
}

function isActivatePayload(value: unknown): value is ActivatePayload {
  return typeof value === 'object' && value !== null && Array.isArray((value as ActivatePayload).claims);
}

function asActivatePayload(result: ToolResultLike): ActivatePayload {
  const payload = expectSuccess<Record<string, unknown>>(result);
  if (!isActivatePayload(payload)) {
    throw new Error(`Unexpected activate payload: ${JSON.stringify(payload, null, 2)}`);
  }
  return payload;
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

function assert(condition: boolean, message: string): asserts condition {
  if (!condition) {
    throw new Error(message);
  }
}

function round(value: number, digits = 4): number {
  return Number(value.toFixed(digits));
}

function percent(value: number): string {
  return `${round(value * 100, 1)}%`;
}

function isoDaysAgo(days: number): string {
  return new Date(NOW.getTime() - days * 24 * 60 * 60 * 1000).toISOString();
}

function average(values: number[]): number {
  if (values.length === 0) return 0;
  return values.reduce((sum, value) => sum + value, 0) / values.length;
}

function cosineSimilarity(a: readonly number[], b: readonly number[]): number {
  assert(a.length === b.length, 'Cosine similarity requires equal vector length');
  let dot = 0;
  let magA = 0;
  let magB = 0;
  for (let index = 0; index < a.length; index++) {
    dot += a[index]! * b[index]!;
    magA += a[index]! * a[index]!;
    magB += b[index]! * b[index]!;
  }
  if (magA === 0 || magB === 0) {
    return 0;
  }
  return dot / Math.sqrt(magA * magB);
}

function buildAverageRanks(values: number[]): number[] {
  const indexed = values.map((value, index) => ({ value, index }));
  indexed.sort((left, right) => right.value - left.value);

  const ranks = new Array<number>(values.length);
  let cursor = 0;
  while (cursor < indexed.length) {
    let end = cursor + 1;
    while (end < indexed.length && indexed[end]!.value === indexed[cursor]!.value) {
      end += 1;
    }
    const averageRank = (cursor + 1 + end) / 2;
    for (let index = cursor; index < end; index++) {
      ranks[indexed[index]!.index] = averageRank;
    }
    cursor = end;
  }
  return ranks;
}

function pearsonCorrelation(left: number[], right: number[]): number {
  assert(left.length === right.length, 'Pearson correlation requires arrays of equal length');
  if (left.length < 2) {
    return 0;
  }
  const meanLeft = average(left);
  const meanRight = average(right);

  let numerator = 0;
  let sumSqLeft = 0;
  let sumSqRight = 0;
  for (let index = 0; index < left.length; index++) {
    const deltaLeft = left[index]! - meanLeft;
    const deltaRight = right[index]! - meanRight;
    numerator += deltaLeft * deltaRight;
    sumSqLeft += deltaLeft * deltaLeft;
    sumSqRight += deltaRight * deltaRight;
  }

  if (sumSqLeft === 0 || sumSqRight === 0) {
    return 0;
  }
  return numerator / Math.sqrt(sumSqLeft * sumSqRight);
}

function spearmanCorrelation(left: number[], right: number[]): number {
  return pearsonCorrelation(buildAverageRanks(left), buildAverageRanks(right));
}

async function setupIsolatedStore(): Promise<EmbeddingService> {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env['PCE_DB'] = ':memory:';
  process.env['PCE_RATE_CAP'] = '100000';
  process.env['PCE_RATE_WINDOW'] = '0';
  process.env['PCE_OBS_STORE_MODE'] = 'raw';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  const embeddingService = createDeterministicEmbeddingService();
  setEmbeddingService(embeddingService);
  expectSuccess(await handlePolicyApply({}));
  return embeddingService;
}

async function rebootRuntimeAgainstCurrentDb(embeddingService: EmbeddingService): Promise<void> {
  resetMemoryState();
  resetLayerScopeState();
  setEmbeddingService(embeddingService);
  await initRateState();
  await resetRates();
  const restored = await initMemoryState()();
  if (isLeft(restored)) {
    throw new Error(restored.left.message);
  }
}

async function seedClaim(input: {
  text: string;
  kind?: ClaimKind;
  scope?: ClaimScope;
  boundary_class?: BoundaryClass;
  memory_type?: MemoryType;
  provenance_at?: string;
  note?: string;
  timestamps?: {
    created_at: string;
    updated_at?: string;
    recency_anchor?: string;
  };
}): Promise<string> {
  const payload = expectSuccess<UpsertPayload>(
    await handleUpsert({
      text: input.text,
      kind: input.kind ?? 'fact',
      scope: input.scope ?? 'project',
      boundary_class: input.boundary_class ?? 'internal',
      memory_type: input.memory_type ?? 'knowledge',
      content_hash: sha256(input.text),
      provenance: {
        at: input.provenance_at ?? new Date().toISOString(),
        actor: 'validation-v3-baseline',
        ...(input.note ? { note: input.note } : {}),
      },
    })
  );

  if (input.timestamps) {
    await updateClaimTimestamps(payload.id, input.timestamps);
  }

  return payload.id;
}

async function seedObservation(input: {
  content: string;
  timestamp?: string;
  boundary_class?: 'public' | 'internal' | 'pii' | 'secret';
}): Promise<string> {
  const payload = expectSuccess<ObservePayload>(
    await handleObserve({
      source_type: 'tool',
      content: input.content,
      boundary_class: input.boundary_class ?? 'internal',
      ttl_days: 30,
      actor: 'validation-v3-baseline',
      extract: { mode: 'noop' },
    })
  );

  if (input.timestamp) {
    await updateObservationCreatedAt(payload.observation_id, input.timestamp);
  }

  return payload.observation_id;
}

async function updateClaimTimestamps(
  claimId: string,
  timestamps: {
    created_at: string;
    updated_at?: string;
    recency_anchor?: string;
  }
): Promise<void> {
  const conn = await getConnection();
  const updatedAt = timestamps.updated_at ?? timestamps.created_at;
  const recencyAnchor = timestamps.recency_anchor ?? updatedAt;
  await conn.run(
    'UPDATE claims SET created_at = $1, updated_at = $2, recency_anchor = $3 WHERE id = $4',
    [timestamps.created_at, updatedAt, recencyAnchor, claimId]
  );
}

async function updateObservationCreatedAt(observationId: string, timestamp: string): Promise<void> {
  const conn = await getConnection();
  await conn.run('UPDATE observations SET created_at = $1 WHERE id = $2', [timestamp, observationId]);
}

async function activate(args: {
  q: string;
  top_k: number;
  intent?: ActivateIntent;
  include_meta?: boolean;
  include_observations?: boolean;
}): Promise<ActivatePayload> {
  return asActivatePayload(
    await handleActivate({
      q: args.q,
      top_k: args.top_k,
      scope: ['project'],
      allow: ALLOW_TAGS,
      ...(args.intent ? { intent: args.intent } : {}),
      ...(args.include_meta !== undefined ? { include_meta: args.include_meta } : {}),
      ...(args.include_observations !== undefined
        ? { include_observations: args.include_observations }
        : {}),
    })
  );
}

function rankMap(payload: ActivatePayload): Map<string, number> {
  return new Map(payload.claims.map((item, index) => [item.claim.id, item.rank ?? index + 1]));
}

async function fetchClaimsByIds(ids: string[]): Promise<Map<string, ClaimRecord>> {
  if (ids.length === 0) {
    return new Map();
  }
  const conn = await getConnection();
  const placeholders = ids.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT id, text, created_at, updated_at, recency_anchor
     FROM claims
     WHERE id IN (${placeholders})`,
    ids
  );
  const rows = reader.getRowObjects() as unknown as ClaimRecord[];
  return new Map(rows.map((row) => [row.id, row]));
}

async function runFreshnessBenchmark(): Promise<FreshnessResult> {
  await setupIsolatedStore();

  for (let index = 0; index < 40; index++) {
    await seedClaim({
      text: `Freshness distractor ${index}: warehouse routing memo for zone ${index} keeps pallet threshold at ${50 + index} units.`,
      provenance_at: isoDaysAgo(30 + index),
      timestamps: {
        created_at: isoDaysAgo(30 + index),
      },
    });
  }

  const cases: BenchmarkCase[] = [];
  const latestWins: number[] = [];
  const top1Wins: number[] = [];

  for (let topic = 0; topic < 10; topic++) {
    const originalId = await seedClaim({
      text: `Freshness topic ${topic}: API timeout for service maple-${topic} is ${15 + topic} seconds under the rollout policy.`,
      provenance_at: isoDaysAgo(120 - topic),
      timestamps: {
        created_at: isoDaysAgo(120 - topic),
      },
    });
    const latestId = await seedClaim({
      text: `Freshness topic ${topic}: API timeout for service maple-${topic} is ${25 + topic} seconds after the rollout update.`,
      provenance_at: isoDaysAgo(2),
      timestamps: {
        created_at: isoDaysAgo(2),
      },
    });

    const query = `service maple-${topic} API timeout rollout policy`;
    const payload = await activate({ q: query, top_k: 4, include_meta: true });
    const ranks = rankMap(payload);
    const originalRank = ranks.get(originalId) ?? Number.POSITIVE_INFINITY;
    const latestRank = ranks.get(latestId) ?? Number.POSITIVE_INFINITY;
    const topId = payload.claims[0]?.claim.id;
    const latestPairWin = latestRank < originalRank;
    const latestTop1 = topId === latestId;

    latestWins.push(latestPairWin ? 1 : 0);
    top1Wins.push(latestTop1 ? 1 : 0);

    cases.push({
      label: `topic_${topic}`,
      query,
      expected_id: latestId,
      actual_ids: payload.claims.map((item) => item.claim.id),
      success: latestTop1,
      notes: `latest_rank=${Number.isFinite(latestRank) ? latestRank : 'miss'} stale_rank=${Number.isFinite(originalRank) ? originalRank : 'miss'}`,
    });
  }

  return {
    name: 'FRESHNESS',
    score: round(average(top1Wins)),
    metric: 'latest_top1_rate',
    expected_baseline: '~50% if the system cannot distinguish stale vs latest versions',
    latest_top1_rate: round(average(top1Wins)),
    latest_pair_win_rate: round(average(latestWins)),
    tracked_topics: 10,
    cases,
  };
}

async function runUsageLearningBenchmark(): Promise<UsageLearningResult> {
  await setupIsolatedStore();

  for (let index = 0; index < 20; index++) {
    await seedClaim({
      text: `Usage distractor ${index}: vendor migration note ${index} for finance export pipelines and checksum rotation.`,
      provenance_at: isoDaysAgo(20 + index),
      timestamps: {
        created_at: isoDaysAgo(20 + index),
      },
    });
  }

  const aliases = [
    'alder',
    'birch',
    'cobalt',
    'dune',
    'ember',
    'fjord',
    'grove',
    'harbor',
    'isotope',
    'juno',
  ] as const;
  const insertionOrder = [6, 1, 8, 0, 9, 3, 5, 2, 7, 4];
  const claimIds = new Map<number, string>();
  for (const label of insertionOrder) {
    const id = await seedClaim({
      text: `Usage learning corpus atlas shared-surface decision note for workspace cedar. Marker ${aliases[label]}.${label === 4 ? ' alwayshot.' : ''}`,
      provenance_at: isoDaysAgo(10 + label),
      timestamps: {
        created_at: isoDaysAgo(10 + label),
      },
    });
    claimIds.set(label, id);
  }

  const retrievalCounts = new Map<number, number>();
  for (let label = 0; label < 10; label++) {
    retrievalCounts.set(label, 0);
  }

  const trainingTargets = [8, 6, 0, 8, 6, 2, 9, 8, 6, 5, 3, 8, 0, 6, 2, 9, 8, 6, 0, 8];
  for (const target of trainingTargets) {
    const payload = await activate({
      q: `Usage learning atlas cedar shared-surface alwayshot ${aliases[target]}`,
      top_k: 2,
    });
    for (const item of payload.claims) {
      for (let label = 0; label < aliases.length; label++) {
        if (item.claim.text.includes(`Marker ${aliases[label]}.`)) {
          retrievalCounts.set(label, (retrievalCounts.get(label) ?? 0) + 1);
          break;
        }
      }
    }
  }

  const finalQuery = 'Usage learning corpus atlas shared-surface decision note workspace cedar';
  const finalPayload = await activate({ q: finalQuery, top_k: 10, include_meta: true });
  const finalRanks = rankMap(finalPayload);

  const labels = Array.from({ length: 10 }, (_, index) => index);
  const frequencyVector = labels.map((label) => retrievalCounts.get(label) ?? 0);
  const relevanceVector = labels.map((label) => {
    const claimId = claimIds.get(label);
    assert(claimId !== undefined, `Missing claim id for usage label ${label}`);
    const rank = finalRanks.get(claimId);
    return rank === undefined ? 0 : 11 - rank;
  });

  const score = spearmanCorrelation(frequencyVector, relevanceVector);

  return {
    name: 'USAGE_LEARNING',
    score: round(score),
    metric: 'spearman_frequency_vs_final_rank',
    expected_baseline: '~0 when activate history does not influence later ranking',
    spearman_frequency_vs_final_rank: round(score),
    final_query: finalQuery,
    tracked_claims: labels.map((label) => {
      const claimId = claimIds.get(label);
      assert(claimId !== undefined, `Missing claim id for usage label ${label}`);
      return {
        id: claimId,
        label: aliases[label],
        retrieval_count: retrievalCounts.get(label) ?? 0,
        final_rank: finalRanks.get(claimId) ?? null,
      };
    }),
  };
}

async function runMaintenanceBenchmark(): Promise<MaintenanceResult> {
  await setupIsolatedStore();

  const duplicateSimilarities: number[] = [];
  for (let pair = 0; pair < 5; pair++) {
    const baseText = `Operations ledger for maple-${pair} shows certificate renewal every 30 days for cluster north.`;
    const nearDuplicateText = `Operations ledger for maple-${pair} shows certificate renewal every 30 days for cluster south.`;
    duplicateSimilarities.push(
      cosineSimilarity(deterministicEmbedding(baseText), deterministicEmbedding(nearDuplicateText))
    );
    await seedClaim({
      text: baseText,
      provenance_at: isoDaysAgo(40 + pair),
      timestamps: {
        created_at: isoDaysAgo(40 + pair),
      },
    });
    await seedClaim({
      text: nearDuplicateText,
      provenance_at: isoDaysAgo(39 + pair),
      timestamps: {
        created_at: isoDaysAgo(39 + pair),
      },
    });
  }

  assert(
    duplicateSimilarities.every((value) => value > 0.9),
    `Expected all maintenance duplicate pairs to exceed 0.9 similarity, got ${duplicateSimilarities.join(', ')}`
  );

  const dormantIds: string[] = [];
  for (let index = 0; index < 40; index++) {
    const id = await seedClaim({
      text: `Maintenance catalog ${index}: release memo for module pine-${index} keeps partition window at ${6 + index} hours.`,
      provenance_at: isoDaysAgo(15 + index),
      timestamps: {
        created_at: isoDaysAgo(15 + index),
      },
    });
    if (index < 5) {
      dormantIds.push(id);
      await updateClaimTimestamps(id, {
        created_at: isoDaysAgo(95 + index),
        updated_at: isoDaysAgo(95 + index),
        recency_anchor: isoDaysAgo(95 + index),
      });
    }
  }

  for (let index = 0; index < 10; index++) {
    await seedObservation({
      content: `Field log ${index}: queue watermark drift noticed for batch oak-${index} after midnight run.`,
      timestamp: isoDaysAgo(1 + index),
    });
  }

  void dormantIds;

  const rawResult = await handleActivate({
    q: 'release memo module partition window',
    top_k: 12,
    scope: ['project'],
    allow: ALLOW_TAGS,
    include_meta: true,
  });
  const payload = asActivatePayload(rawResult);
  const responseText = JSON.stringify(rawResult.structuredContent ?? parseToolContent(rawResult));

  const categoryMatchers: Record<string, RegExp> = {
    duplicate: /\bduplicate\b|\bnear[- ]duplicate\b/i,
    observation_backlog: /\bobservation\b|\bunprocessed\b|\bbacklog\b/i,
    dormant_claims: /\bstale\b|\bdormant\b|\bunused\b|\bnever retrieved\b/i,
  };

  const detectedCategories = Object.entries(categoryMatchers)
    .filter(([, pattern]) => pattern.test(responseText))
    .map(([category]) => category);
  const checkedCategories = Object.keys(categoryMatchers);

  return {
    name: 'MAINTENANCE',
    score: round(detectedCategories.length / checkedCategories.length),
    metric: 'detected_hint_category_ratio',
    expected_baseline: '0 because activate does not currently surface maintenance guidance',
    detected_hint_category_ratio: round(detectedCategories.length / checkedCategories.length),
    detected_categories: detectedCategories,
    checked_categories: checkedCategories,
    activate_keys: Object.keys(payload),
    response_excerpt: responseText.slice(0, 400),
  };
}

async function runConnectivityBenchmark(): Promise<ConnectivityResult> {
  await setupIsolatedStore();

  const cases: BenchmarkCase[] = [];
  const recalls: number[] = [];

  for (let topic = 0; topic < 10; topic++) {
    const anchorId = await seedClaim({
      text: `Connectivity anchor ${topic}: maple-${topic} login tokens require issuer validation and short session expiry.`,
      provenance_at: isoDaysAgo(25 + topic),
      timestamps: {
        created_at: isoDaysAgo(25 + topic),
      },
    });
    const relatedId = await seedClaim({
      text: `Connectivity extension ${topic}: maple-${topic} refresh rotation extends login token controls with revocation windows and renewal ledgers.`,
      provenance_at: isoDaysAgo(20 + topic),
      timestamps: {
        created_at: isoDaysAgo(20 + topic),
      },
    });

    const payload = await activate({
      q: `maple-${topic} login tokens issuer validation`,
      top_k: 5,
      include_meta: true,
    });
    const actualIds = payload.claims.map((item) => item.claim.id);
    const success = actualIds.includes(relatedId);
    recalls.push(success ? 1 : 0);

    cases.push({
      label: `topic_${topic}`,
      query: `maple-${topic} login tokens issuer validation`,
      expected_id: relatedId,
      actual_ids: actualIds,
      success,
      notes: `anchor_id=${anchorId}`,
    });
  }

  return {
    name: 'CONNECTIVITY',
    score: round(average(recalls)),
    metric: 'related_claim_recall_at_5',
    expected_baseline: 'Low recall unless the related claim also overlaps lexically with the query',
    related_claim_recall_at_5: round(average(recalls)),
    pair_count: 10,
    cases,
  };
}

async function runCombinedBenchmark(): Promise<CombinedResult> {
  const embeddingService = await setupIsolatedStore();

  const updatedFamilies: Array<{ stale: string; latest?: string }> = [];
  const retainedRelevantIds: string[] = [];

  for (let index = 0; index < 15; index++) {
    const topic =
      index < 5
        ? `auth`
        : index < 10
          ? `billing`
          : `observability`;
    const text =
      topic === 'auth'
        ? `Session one auth memo ${index}: cedar login flow keeps token guardrail ${index} and issuer checks for design review.`
        : topic === 'billing'
          ? `Session one billing memo ${index}: invoice export lane ${index} keeps nightly checksum validation for finance review.`
          : `Session one observability memo ${index}: alert lane ${index} keeps dashboard retention at ${14 + index} days.`;
    const id = await seedClaim({
      text,
      provenance_at: isoDaysAgo(45 - index),
      timestamps: {
        created_at: isoDaysAgo(45 - index),
      },
    });
    if (topic === 'auth' && index >= 3) {
      retainedRelevantIds.push(id);
    }
    if (topic === 'auth' && index < 3) {
      updatedFamilies.push({ stale: id });
    }
  }

  await rebootRuntimeAgainstCurrentDb(embeddingService);

  const newRelevantIds: string[] = [];
  const authDistractorIds: string[] = [];
  for (let index = 0; index < updatedFamilies.length; index++) {
    const latestId = await seedClaim({
      text: `Session two auth memo ${index}: cedar login flow now adds rotation windows, revocation ledgers, and issuer checks for design review.`,
      provenance_at: isoDaysAgo(2),
      timestamps: {
        created_at: isoDaysAgo(2),
      },
    });
    updatedFamilies[index]!.latest = latestId;
  }

  for (let index = 0; index < 10; index++) {
    const authRelevant = index < 3;
    const authDistractor = index >= 3 && index < 6;
    const text =
      authRelevant
        ? `Session two auth extension ${index}: cedar login design adds rotation rollout note ${index}, token revocation drill, and recovery checklist.`
        : authDistractor
          ? `Session two auth distractor ${index}: cedar login support note ${index} covers FAQ edits, onboarding copy, and temporary access banners.`
          : `Session two distractor ${index}: procurement note ${index} keeps vendor attestations in quarterly archive review.`;
    const id = await seedClaim({
      text,
      provenance_at: isoDaysAgo(3 + index),
      timestamps: {
        created_at: isoDaysAgo(3 + index),
      },
    });
    if (authRelevant) {
      newRelevantIds.push(id);
    }
    if (authDistractor) {
      authDistractorIds.push(id);
    }
  }

  await rebootRuntimeAgainstCurrentDb(embeddingService);

  const finalQuery = 'cedar login token rotation issuer design review';
  const payload = await activate({
    q: finalQuery,
    top_k: 8,
    intent: 'design_decision',
    include_meta: true,
  });
  const ranks = rankMap(payload);

  const freshnessScores = updatedFamilies.map((family) => {
    assert(family.latest !== undefined, 'Expected latest claim id in combined benchmark');
    const staleRank = ranks.get(family.stale) ?? Number.POSITIVE_INFINITY;
    const latestRank = ranks.get(family.latest) ?? Number.POSITIVE_INFINITY;
    return latestRank < staleRank ? 1 : 0;
  });

  const expectedRelevantIds = [
    ...updatedFamilies.map((family) => {
      assert(family.latest !== undefined, 'Expected latest claim id in combined benchmark');
      return family.latest;
    }),
    ...newRelevantIds,
  ];

  void authDistractorIds;
  void retainedRelevantIds;

  const finalResultIds = payload.claims.map((item) => item.claim.id);
  const hits = finalResultIds.filter((id) => expectedRelevantIds.includes(id)).length;
  const relevancePrecisionAt8 = hits / 8;
  const freshnessPairAccuracy = average(freshnessScores);

  return {
    name: 'COMBINED',
    score: round((freshnessPairAccuracy + relevancePrecisionAt8) / 2),
    metric: 'mean(freshness_pair_accuracy,relevance_precision_at_8)',
    expected_baseline: 'Composite of freshness and relevance under a multi-session workload',
    freshness_pair_accuracy: round(freshnessPairAccuracy),
    relevance_precision_at_8: round(relevancePrecisionAt8),
    final_query: finalQuery,
    final_result_ids: finalResultIds,
    expected_relevant_ids: expectedRelevantIds,
  };
}

function buildReport(results: BenchmarkResults): string {
  const { B1, B2, B3, B4, B5 } = results.benchmarks;
  return [
    '# V3 Baseline Benchmark',
    '',
    `Generated at: ${results.generated_at}`,
    '',
    'This benchmark uses internal handler imports from `apps/pce-memory/src/`, an isolated `:memory:` DuckDB store per dimension, and a deterministic bag-of-words embedding service for repeatable local execution.',
    '',
    '## Score Summary',
    '',
    '| Dimension | Score | Metric |',
    '| --- | ---: | --- |',
    `| B1 Freshness | ${percent(B1.score)} | latest top-1 is newest version |`,
    `| B2 Usage Learning | ${round(B2.score, 3)} | Spearman(freq, final rank) |`,
    `| B3 Maintenance | ${percent(B3.score)} | detected hint categories |`,
    `| B4 Connectivity | ${percent(B4.score)} | related claim recall@5 |`,
    `| B5 Combined | ${percent(B5.score)} | mean(freshness,relevance) |`,
    '',
    '## Notes',
    '',
    `- B1 latest top-1 rate: ${percent(B1.latest_top1_rate)}. Pairwise latest-vs-stale win rate: ${percent(B1.latest_pair_win_rate)}.`,
    `- B2 final correlation: ${round(B2.spearman_frequency_vs_final_rank, 3)}.`,
    `- B3 detected categories: ${B3.detected_categories.length === 0 ? 'none' : B3.detected_categories.join(', ')}.`,
    `- B4 related claim recall@5: ${percent(B4.related_claim_recall_at_5)}.`,
    `- B5 freshness pair accuracy: ${percent(B5.freshness_pair_accuracy)}. Relevance precision@8: ${percent(B5.relevance_precision_at_8)}.`,
    '',
    '## Interpretation',
    '',
    '- B1 is the baseline for future freshness-aware retrieval. Higher post-v3 scores should mean newer claims displace stale variants more reliably.',
    '- B2 isolates usage learning without feedback writes. A post-v3 implementation should move the correlation positive only if plain retrieval history becomes a ranking signal.',
    '- B3 checks whether activate currently surfaces maintenance guidance for duplicates, raw observations, or dormant claims. The current baseline is expected to stay at zero unless new hint fields are introduced.',
    '- B4 measures how often logically related claims appear without graph links. Improvements after connectivity work should raise recall without relying on lexical coincidence.',
    '- B5 gives a single regression-friendly number for a realistic multi-session flow.',
    '',
  ].join('\n');
}

async function writeArtifacts(results: BenchmarkResults): Promise<void> {
  await fs.mkdir(RESULTS_DIR, { recursive: true });
  await fs.writeFile(RESULTS_JSON_PATH, `${JSON.stringify(results, null, 2)}\n`, 'utf8');
  await fs.writeFile(REPORT_PATH, `${buildReport(results)}\n`, 'utf8');
}

async function main(): Promise<void> {
  try {
    const results: BenchmarkResults = {
      generated_at: new Date().toISOString(),
      environment: {
        repo_root: REPO_ROOT,
        node: process.version,
        database: ':memory:',
        embedding_service: 'deterministic-bow-v1',
        internal_handlers: true,
      },
      benchmarks: {
        B1: await runFreshnessBenchmark(),
        B2: await runUsageLearningBenchmark(),
        B3: await runMaintenanceBenchmark(),
        B4: await runConnectivityBenchmark(),
        B5: await runCombinedBenchmark(),
      },
    };

    await writeArtifacts(results);

    console.log(`Wrote ${RESULTS_JSON_PATH}`);
    console.log(`Wrote ${REPORT_PATH}`);
  } finally {
    await closeDb();
  }
}

await main();

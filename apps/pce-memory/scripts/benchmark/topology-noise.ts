import { performance } from 'node:perf_hooks';
import { computeContentHash } from '@pce/embeddings';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection.js';
import { resetLayerScopeState } from '../../src/state/layerScopeState.js';
import { resetMemoryState } from '../../src/state/memoryState.js';
import { linkClaimEntity, upsertEntity } from '../../src/store/entities.js';
import { setEmbeddingService } from '../../src/store/hybridSearch.js';
import { initRateState, resetRates } from '../../src/store/rate.js';
import { upsertRelation } from '../../src/store/relations.js';
import {
  createBenchmarkEmbeddingService,
  withRestoredEmbeddingService,
} from './embeddingService.js';
import { dispatchToolOrThrow } from './toolResult.js';

interface ActivateClaimResult {
  claim: { id: string };
  source?: string;
  topology?: {
    kind?: string;
    depth?: number;
    path?: Array<{
      kind?: string;
      from_claim_id?: string;
      to_claim_id?: string;
    }>;
  };
}

interface ScenarioSeed {
  query: string;
  topK: number;
  relevantIds: string[];
  labelById: Record<string, string>;
  diagnostics?: Record<string, unknown>;
  probeTopK?: number;
}

interface ScenarioDefinition {
  name: string;
  description: string;
  seed: () => Promise<ScenarioSeed>;
}

type SweepCaseParams = Record<string, number>;

interface SweepCaseDefinition {
  params: SweepCaseParams;
  seed: () => Promise<ScenarioSeed>;
}

interface SweepDefinition {
  name: string;
  description: string;
  cases: SweepCaseDefinition[];
}

interface VariantMetrics {
  precision_at_k: number;
  recall_at_k: number;
  avg_latency_ms: number;
  result_count: number;
  noise_count: number;
  graph_source_count: number;
  graph_source_share: number;
  top_claim_ids: string[];
  top_claim_labels: string[];
  top_claim_sources: string[];
  noise_labels: string[];
  graph_claim_details: Array<{
    label: string;
    source: string;
    depth: number | null;
    path_kinds: string[];
  }>;
  probe_graph_claim_details: Array<{
    label: string;
    source: string;
    depth: number | null;
    path_kinds: string[];
  }>;
}

interface DeltaMetrics {
  precision_at_k: number;
  recall_at_k: number;
  avg_latency_ms: number;
  noise_count: number;
  graph_source_count: number;
  graph_source_share: number;
}

interface ActivateVariantOptions {
  disableGraphPresenceInjection?: boolean;
}

export interface TopologyNoiseScenarioReport {
  name: string;
  description: string;
  top_k: number;
  relevant_labels: string[];
  baseline: VariantMetrics;
  natural_topology: VariantMetrics;
  topology: VariantMetrics;
  natural_deltas: DeltaMetrics;
  deltas: DeltaMetrics;
  injection_deltas: DeltaMetrics;
  diagnostics?: Record<string, unknown>;
}

export interface TopologyNoiseSweepCaseReport {
  params: SweepCaseParams;
  top_k: number;
  relevant_labels: string[];
  baseline: VariantMetrics;
  natural_topology: VariantMetrics;
  topology: VariantMetrics;
  natural_deltas: DeltaMetrics;
  deltas: DeltaMetrics;
  injection_deltas: DeltaMetrics;
  diagnostics?: Record<string, unknown>;
}

export interface TopologyNoiseSweepReport {
  name: string;
  description: string;
  summary: {
    case_count: number;
    precision_drop_cases: number;
    recall_drop_cases: number;
    increased_noise_cases: number;
    injection_worsened_cases: number;
    max_precision_drop: number;
    max_injection_precision_drop: number;
    max_graph_source_share: number;
  };
  cases: TopologyNoiseSweepCaseReport[];
}

export interface TopologyNoiseBenchmarkReport {
  generated_at: string;
  environment: {
    node: string;
    platform: string;
  };
  summary: {
    scenario_count: number;
    sweep_count: number;
    sweep_case_count: number;
    precision_drop_scenarios: number;
    recall_drop_scenarios: number;
    increased_noise_scenarios: number;
    injection_worsened_scenarios: number;
    precision_drop_sweep_cases: number;
    recall_drop_sweep_cases: number;
    increased_noise_sweep_cases: number;
    injection_worsened_sweep_cases: number;
    avg_precision_delta: number;
    avg_recall_delta: number;
    avg_latency_delta_ms: number;
    avg_injection_precision_delta: number;
    max_precision_drop: number;
    max_sweep_precision_drop: number;
    max_injection_precision_drop: number;
  };
  scenarios: TopologyNoiseScenarioReport[];
  sweeps: TopologyNoiseSweepReport[];
}

const ANCHOR_REPEATS = 8;
const SWEEP_REPEATS = 1;

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function directVector(rank: number): readonly number[] {
  return normalize([1 - rank * 0.025, Math.max(0.01, rank * 0.02)]);
}

function bridgeVector(): readonly number[] {
  return normalize([0.32, 0.68]);
}

function noiseVector(): readonly number[] {
  return normalize([0, 1]);
}

async function resetBenchmarkState(): Promise<void> {
  setEmbeddingService(null);
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '1000';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

function buildPolicyYaml(topologyEnabled: boolean): string {
  return `
version: '0.1'
boundary:
  version: '0.1'
  scopes:
    session: { ttl: '7d' }
    project: { ttl: '120d' }
    principle: { ttl: 'inf' }
  boundary_classes:
    public: { allow: ['*'] }
    internal: { allow: ['answer:task', 'tool:*'] }
    pii:
      allow: ['tool:contact-lookup']
      redact: ['email', 'phone']
      escalation: 'human_review'
    secret: { allow: [], escalation: 'deny' }
retrieval:
  hybrid:
    alpha: 0.65
    threshold: 0.15
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
    topology:
      enabled: ${topologyEnabled}
maintenance:
  hints_enabled: true
  similarity_threshold: 0.9
  stale_days: 30
`.trim();
}

async function applyPolicy(topologyEnabled: boolean): Promise<void> {
  await dispatchToolOrThrow('pce_memory_policy_apply', {
    yaml: buildPolicyYaml(topologyEnabled),
  });
}

async function upsertKnowledge(text: string): Promise<string> {
  const result = await dispatchToolOrThrow<{ id: string }>('pce_memory_upsert', {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'benchmark' },
  });
  return result.id;
}

async function runMeasuredActivate(
  query: string,
  topK: number,
  repeats: number,
  options: ActivateVariantOptions = {},
  probeTopK?: number
): Promise<{
  claims: ActivateClaimResult[];
  avgLatencyMs: number;
  probeClaims: ActivateClaimResult[];
}> {
  const first = await dispatchToolOrThrow<{
    claims: ActivateClaimResult[];
  }>('pce_memory_activate', {
    scope: ['project'],
    allow: ['answer:task'],
    q: query,
    top_k: topK,
    ...(options.disableGraphPresenceInjection
      ? { debug_disable_graph_presence_injection: true }
      : {}),
  });

  const samples: number[] = [];
  for (let index = 0; index < repeats; index++) {
    const startedAt = performance.now();
    await dispatchToolOrThrow('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: query,
      top_k: topK,
      ...(options.disableGraphPresenceInjection
        ? { debug_disable_graph_presence_injection: true }
        : {}),
    });
    samples.push(performance.now() - startedAt);
  }

  const probeClaims =
    typeof probeTopK === 'number' && probeTopK > topK
      ? ((
          await dispatchToolOrThrow<{
            claims: ActivateClaimResult[];
          }>('pce_memory_activate', {
            scope: ['project'],
            allow: ['answer:task'],
            q: query,
            top_k: probeTopK,
            ...(options.disableGraphPresenceInjection
              ? { debug_disable_graph_presence_injection: true }
              : {}),
          })
        ).claims ?? first.claims)
      : first.claims;

  return {
    claims: first.claims,
    avgLatencyMs: samples.reduce((sum, value) => sum + value, 0) / Math.max(samples.length, 1),
    probeClaims,
  };
}

function measureTopK(
  claims: ActivateClaimResult[],
  probeClaims: ActivateClaimResult[],
  relevantIds: readonly string[],
  labelById: Record<string, string>,
  k: number
): VariantMetrics {
  const top = claims.slice(0, k);
  const relevant = new Set(relevantIds);
  const matched = top.filter((item) => relevant.has(item.claim.id));
  const graphSourceCount = top.filter(
    (item) => item.source === 'claim_link' || item.source === 'topology'
  ).length;
  const noiseLabels = top
    .filter((item) => !relevant.has(item.claim.id))
    .map((item) => labelById[item.claim.id] ?? item.claim.id);
  const graphClaimDetails = top
    .filter((item) => item.source === 'claim_link' || item.source === 'topology')
    .map((item) => ({
      label: labelById[item.claim.id] ?? item.claim.id,
      source: item.source ?? 'search',
      depth: typeof item.topology?.depth === 'number' ? item.topology.depth : null,
      path_kinds: (item.topology?.path ?? [])
        .map((segment) => segment.kind)
        .filter((kind): kind is string => typeof kind === 'string'),
    }));
  const probeGraphClaimDetails = probeClaims
    .filter((item) => item.source === 'claim_link' || item.source === 'topology')
    .map((item) => ({
      label: labelById[item.claim.id] ?? item.claim.id,
      source: item.source ?? 'search',
      depth: typeof item.topology?.depth === 'number' ? item.topology.depth : null,
      path_kinds: (item.topology?.path ?? [])
        .map((segment) => segment.kind)
        .filter((kind): kind is string => typeof kind === 'string'),
    }));

  return {
    precision_at_k: matched.length / k,
    recall_at_k: relevant.size === 0 ? 0 : matched.length / relevant.size,
    avg_latency_ms: 0,
    result_count: claims.length,
    noise_count: noiseLabels.length,
    graph_source_count: graphSourceCount,
    graph_source_share: Number((graphSourceCount / Math.max(k, 1)).toFixed(3)),
    top_claim_ids: top.map((item) => item.claim.id),
    top_claim_labels: top.map((item) => labelById[item.claim.id] ?? item.claim.id),
    top_claim_sources: top.map((item) => item.source ?? 'search'),
    noise_labels: noiseLabels,
    graph_claim_details: graphClaimDetails,
    probe_graph_claim_details: probeGraphClaimDetails,
  };
}

function computeDeltas(baseline: VariantMetrics, topology: VariantMetrics): DeltaMetrics {
  return {
    precision_at_k: Number((topology.precision_at_k - baseline.precision_at_k).toFixed(3)),
    recall_at_k: Number((topology.recall_at_k - baseline.recall_at_k).toFixed(3)),
    avg_latency_ms: Number((topology.avg_latency_ms - baseline.avg_latency_ms).toFixed(3)),
    noise_count: topology.noise_count - baseline.noise_count,
    graph_source_count: topology.graph_source_count - baseline.graph_source_count,
    graph_source_share: Number(
      (topology.graph_source_share - baseline.graph_source_share).toFixed(3)
    ),
  };
}

function summarizeSweepCases(
  cases: TopologyNoiseSweepCaseReport[]
): TopologyNoiseSweepReport['summary'] {
  const precisionDrops = cases.map((caseReport) => Math.min(0, caseReport.deltas.precision_at_k));
  const injectionPrecisionDrops = cases.map((caseReport) =>
    Math.min(0, caseReport.injection_deltas.precision_at_k)
  );

  return {
    case_count: cases.length,
    precision_drop_cases: cases.filter((caseReport) => caseReport.deltas.precision_at_k < 0).length,
    recall_drop_cases: cases.filter((caseReport) => caseReport.deltas.recall_at_k < 0).length,
    increased_noise_cases: cases.filter((caseReport) => caseReport.deltas.noise_count > 0).length,
    injection_worsened_cases: cases.filter(
      (caseReport) => caseReport.injection_deltas.precision_at_k < 0
    ).length,
    max_precision_drop: Number(
      Math.max(...precisionDrops.map((value) => Math.abs(value)), 0).toFixed(3)
    ),
    max_injection_precision_drop: Number(
      Math.max(...injectionPrecisionDrops.map((value) => Math.abs(value)), 0).toFixed(3)
    ),
    max_graph_source_share: Number(
      Math.max(...cases.map((caseReport) => caseReport.topology.graph_source_share), 0).toFixed(3)
    ),
  };
}

function expandParameterGrid(dimensions: Record<string, readonly number[]>): SweepCaseParams[] {
  const entries = Object.entries(dimensions);
  return entries.reduce<SweepCaseParams[]>(
    (rows, [name, values]) =>
      rows.flatMap((row) =>
        values.map((value) => ({
          ...row,
          [name]: value,
        }))
      ),
    [{}]
  );
}

async function runScenarioVariant(
  definition: ScenarioDefinition,
  topologyEnabled: boolean,
  repeats: number,
  options: ActivateVariantOptions = {}
): Promise<{
  metrics: VariantMetrics;
  topK: number;
  relevantLabels: string[];
  diagnostics?: Record<string, unknown>;
}> {
  await resetBenchmarkState();
  await applyPolicy(topologyEnabled);
  const seeded = await definition.seed();
  const measured = await runMeasuredActivate(
    seeded.query,
    seeded.topK,
    repeats,
    options,
    seeded.probeTopK
  );
  const metrics = measureTopK(
    measured.claims,
    measured.probeClaims,
    seeded.relevantIds,
    seeded.labelById,
    seeded.topK
  );
  metrics.avg_latency_ms = Number(measured.avgLatencyMs.toFixed(3));

  return {
    metrics,
    topK: seeded.topK,
    relevantLabels: seeded.relevantIds.map((id) => seeded.labelById[id] ?? id),
    diagnostics: seeded.diagnostics,
  };
}

async function runSweepCaseVariant(
  definition: SweepCaseDefinition,
  topologyEnabled: boolean,
  repeats: number,
  options: ActivateVariantOptions = {}
): Promise<{
  metrics: VariantMetrics;
  topK: number;
  relevantLabels: string[];
  diagnostics?: Record<string, unknown>;
}> {
  await resetBenchmarkState();
  await applyPolicy(topologyEnabled);
  const seeded = await definition.seed();
  const measured = await runMeasuredActivate(
    seeded.query,
    seeded.topK,
    repeats,
    options,
    seeded.probeTopK
  );
  const metrics = measureTopK(
    measured.claims,
    measured.probeClaims,
    seeded.relevantIds,
    seeded.labelById,
    seeded.topK
  );
  metrics.avg_latency_ms = Number(measured.avgLatencyMs.toFixed(3));

  return {
    metrics,
    topK: seeded.topK,
    relevantLabels: seeded.relevantIds.map((id) => seeded.labelById[id] ?? id),
    diagnostics: seeded.diagnostics,
  };
}

async function seedForcedPresenceNoiseScenario(): Promise<ScenarioSeed> {
  const seedText = 'Issuer validation anchor for partner authentication policy.';
  const directRelevantText =
    'Issuer validation reference checklist for partner authentication rollout.';
  const noisyRelatedText = 'Quarterly offsite catering schedule for office events and seating.';
  const queryText = 'issuer validation partner authentication';

  setEmbeddingService(
    createBenchmarkEmbeddingService(
      {
        [seedText]: normalize([1, 0]),
        [directRelevantText]: normalize([0.94, 0.06]),
        [noisyRelatedText]: noiseVector(),
        [queryText]: normalize([1, 0]),
      },
      {
        fallbackEmbedding: normalize([-1, 0]),
        modelVersion: 'topology-noise-benchmark-v2',
      }
    )
  );

  const seedId = await upsertKnowledge(seedText);
  const directRelevantId = await upsertKnowledge(directRelevantText);
  const noisyRelatedId = await upsertKnowledge(noisyRelatedText);

  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: noisyRelatedId,
    target_claim_id: seedId,
    link_type: 'related',
    confidence: 1,
  });

  return {
    query: queryText,
    topK: 2,
    relevantIds: [seedId, directRelevantId],
    labelById: {
      [seedId]: 'seed',
      [directRelevantId]: 'direct-relevant',
      [noisyRelatedId]: 'noisy-related',
    },
  };
}

async function seedGenericHubNoiseScenario(): Promise<ScenarioSeed> {
  const seedText = 'OAuth issuer validation anchor for mobile auth service.';
  const directRelevantText = 'OAuth issuer validation deployment guide for mobile auth service.';
  const hubNoiseText = 'Brand campaign notes for sponsorship planning and poster review.';
  const queryText = 'oauth issuer validation mobile auth service';

  setEmbeddingService(
    createBenchmarkEmbeddingService(
      {
        [seedText]: normalize([1, 0]),
        [directRelevantText]: normalize([0.93, 0.07]),
        [hubNoiseText]: noiseVector(),
        [queryText]: normalize([1, 0]),
      },
      {
        fallbackEmbedding: normalize([-1, 0]),
        modelVersion: 'topology-noise-benchmark-v2',
      }
    )
  );

  const seedId = await upsertKnowledge(seedText);
  const directRelevantId = await upsertKnowledge(directRelevantText);
  const hubNoiseId = await upsertKnowledge(hubNoiseText);

  const genericHub = await upsertEntity({
    id: 'ent_noise_general_hub',
    type: 'Concept',
    name: 'General',
    canonical_key: 'general',
  });
  const campaignEntity = await upsertEntity({
    id: 'ent_noise_campaign',
    type: 'Artifact',
    name: 'Campaign Plan',
    canonical_key: 'campaign-plan',
  });

  await linkClaimEntity(seedId, genericHub.id);
  await linkClaimEntity(hubNoiseId, campaignEntity.id);
  await upsertRelation({
    id: 'rel_noise_general_to_campaign',
    src_id: genericHub.id,
    dst_id: campaignEntity.id,
    type: 'ASSOCIATED_WITH',
  });

  const audit = await dispatchToolOrThrow<{
    findings: Array<{ kind: string; node_ids?: string[] }>;
  }>('pce_memory_graph_audit', {
    generic_hub_degree_threshold: 2,
    max_findings_per_kind: 10,
  });
  const genericHubDetected = audit.findings.some(
    (finding) => finding.kind === 'generic_hub' && finding.node_ids?.includes(genericHub.id)
  );

  return {
    query: queryText,
    topK: 2,
    relevantIds: [seedId, directRelevantId],
    labelById: {
      [seedId]: 'seed',
      [directRelevantId]: 'direct-relevant',
      [hubNoiseId]: 'hub-noise',
    },
    diagnostics: {
      generic_hub_detected: genericHubDetected,
    },
  };
}

async function seedConfidenceMitigatedScenario(): Promise<ScenarioSeed> {
  const seedText = 'Session revocation anchor for customer security controls.';
  const directRelevantText = 'Session revocation rollout guide for customer security controls.';
  const directDistractorText = 'Session revocation dashboard copy review for launch messaging.';
  const relevantLinkedText = 'Refresh token family revocation prevents replay after device theft.';
  const noisyLinkedText = 'Facilities keycard replacement checklist for office visitors.';
  const queryText = 'session revocation customer security controls';

  setEmbeddingService(
    createBenchmarkEmbeddingService(
      {
        [seedText]: normalize([1, 0]),
        [directRelevantText]: normalize([0.95, 0.05]),
        [directDistractorText]: normalize([0.8, 0.2]),
        [relevantLinkedText]: noiseVector(),
        [noisyLinkedText]: noiseVector(),
        [queryText]: normalize([1, 0]),
      },
      {
        fallbackEmbedding: normalize([-1, 0]),
        modelVersion: 'topology-noise-benchmark-v2',
      }
    )
  );

  const seedId = await upsertKnowledge(seedText);
  const directRelevantId = await upsertKnowledge(directRelevantText);
  const directDistractorId = await upsertKnowledge(directDistractorText);
  const relevantLinkedId = await upsertKnowledge(relevantLinkedText);
  const noisyLinkedId = await upsertKnowledge(noisyLinkedText);

  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: relevantLinkedId,
    target_claim_id: seedId,
    link_type: 'related',
    confidence: 1,
  });
  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: noisyLinkedId,
    target_claim_id: seedId,
    link_type: 'related',
    confidence: 0.05,
  });

  return {
    query: queryText,
    topK: 3,
    relevantIds: [seedId, directRelevantId, relevantLinkedId],
    labelById: {
      [seedId]: 'seed',
      [directRelevantId]: 'direct-relevant',
      [directDistractorId]: 'direct-distractor',
      [relevantLinkedId]: 'relevant-linked',
      [noisyLinkedId]: 'noisy-linked',
    },
  };
}

async function seedRelatedStarSweepCase(params: SweepCaseParams): Promise<ScenarioSeed> {
  const topK = params.top_k!;
  const confidence = params.confidence!;
  const fanout = params.fanout!;
  const queryText = 'issuer validation partner authentication';
  const directTexts = [
    'Issuer validation anchor for partner authentication policy.',
    'Issuer validation deployment checklist for partner authentication gateway.',
    'Issuer validation migration notes for partner authentication enforcement.',
    'Issuer validation exception handling for partner authentication rollout.',
    'Issuer validation audit evidence for partner authentication program.',
  ];
  const noiseTexts = Array.from(
    { length: fanout },
    (_, index) => `Office lunch seating plan ${index} for catering and badge pickup.`
  );

  const embeddings: Record<string, readonly number[]> = {
    [queryText]: normalize([1, 0]),
  };
  for (const [index, text] of directTexts.entries()) {
    embeddings[text] = directVector(index);
  }
  for (const text of noiseTexts) {
    embeddings[text] = noiseVector();
  }
  setEmbeddingService(
    createBenchmarkEmbeddingService(embeddings, {
      fallbackEmbedding: normalize([-1, 0]),
      modelVersion: 'topology-noise-benchmark-v2',
    })
  );

  const directIds: string[] = [];
  const labelById: Record<string, string> = {};
  for (const [index, text] of directTexts.entries()) {
    const id = await upsertKnowledge(text);
    directIds.push(id);
    labelById[id] = index === 0 ? 'seed' : `direct-${index}`;
  }
  const seedId = directIds[0]!;

  for (const [index, text] of noiseTexts.entries()) {
    const noiseId = await upsertKnowledge(text);
    labelById[noiseId] = `related-noise-${index + 1}`;
    await dispatchToolOrThrow('pce_memory_link_claims', {
      source_claim_id: noiseId,
      target_claim_id: seedId,
      link_type: 'related',
      confidence,
    });
  }

  return {
    query: queryText,
    topK,
    relevantIds: directIds.slice(0, topK),
    labelById,
  };
}

async function seedGenericHubSweepCase(params: SweepCaseParams): Promise<ScenarioSeed> {
  const topK = params.top_k!;
  const fanout = params.fanout!;
  const queryText = 'oauth issuer validation mobile auth service';
  const directTexts = Array.from(
    { length: 10 },
    (_, index) => `OAuth issuer validation control ${index} for mobile auth service release safety.`
  );
  const noiseTexts = Array.from(
    { length: fanout },
    (_, index) => `Brand campaign planning note ${index} for booth poster approvals.`
  );

  const embeddings: Record<string, readonly number[]> = {
    [queryText]: normalize([1, 0]),
  };
  for (const [index, text] of directTexts.entries()) {
    embeddings[text] = directVector(index);
  }
  for (const text of noiseTexts) {
    embeddings[text] = noiseVector();
  }
  setEmbeddingService(
    createBenchmarkEmbeddingService(embeddings, {
      fallbackEmbedding: normalize([-1, 0]),
      modelVersion: 'topology-noise-benchmark-v2',
    })
  );

  const directIds: string[] = [];
  const labelById: Record<string, string> = {};
  for (const [index, text] of directTexts.entries()) {
    const id = await upsertKnowledge(text);
    directIds.push(id);
    labelById[id] = index === 0 ? 'seed' : `direct-${index}`;
  }
  const seedId = directIds[0]!;

  const genericHub = await upsertEntity({
    id: `ent_generic_hub_${fanout}_${topK}`,
    type: 'Concept',
    name: 'General',
    canonical_key: `general-${fanout}-${topK}`,
  });
  await linkClaimEntity(seedId, genericHub.id);

  for (const [index, text] of noiseTexts.entries()) {
    const noiseId = await upsertKnowledge(text);
    labelById[noiseId] = `hub-noise-${index + 1}`;
    const noiseEntity = await upsertEntity({
      id: `ent_hub_noise_${fanout}_${topK}_${index}`,
      type: 'Artifact',
      name: `Campaign Artifact ${index}`,
      canonical_key: `campaign-artifact-${fanout}-${topK}-${index}`,
    });
    await linkClaimEntity(noiseId, noiseEntity.id);
    await upsertRelation({
      id: `rel_hub_noise_${fanout}_${topK}_${index}`,
      src_id: genericHub.id,
      dst_id: noiseEntity.id,
      type: 'ASSOCIATED_WITH',
    });
  }

  return {
    query: queryText,
    topK,
    relevantIds: directIds.slice(0, topK),
    labelById,
  };
}

async function seedTwoHopSweepCase(params: SweepCaseParams): Promise<ScenarioSeed> {
  const topK = params.top_k!;
  const confidence = params.confidence!;
  const fanout = params.fanout!;
  const queryText = 'session revocation customer security controls';
  const directTexts = [
    'Session revocation anchor for customer security controls.',
    'Session revocation deployment guide for customer security controls.',
    'Session revocation audit checklist for customer security controls.',
    'Session revocation rollback notes for customer security controls.',
    'Session revocation alert routing for customer security controls.',
    'Session revocation ownership map for customer security controls.',
  ];
  const bridgeText = 'Refresh token family revocation bridge for device theft recovery.';
  const noiseTexts = Array.from(
    { length: fanout },
    (_, index) => `Facilities key inventory note ${index} for guest parking permits.`
  );

  const embeddings: Record<string, readonly number[]> = {
    [queryText]: normalize([1, 0]),
    [bridgeText]: bridgeVector(),
  };
  for (const [index, text] of directTexts.entries()) {
    embeddings[text] = directVector(index);
  }
  for (const text of noiseTexts) {
    embeddings[text] = noiseVector();
  }
  setEmbeddingService(
    createBenchmarkEmbeddingService(embeddings, {
      fallbackEmbedding: normalize([-1, 0]),
      modelVersion: 'topology-noise-benchmark-v2',
    })
  );

  const directIds: string[] = [];
  const labelById: Record<string, string> = {};
  for (const [index, text] of directTexts.entries()) {
    const id = await upsertKnowledge(text);
    directIds.push(id);
    labelById[id] = index === 0 ? 'seed' : `direct-${index}`;
  }
  const seedId = directIds[0]!;
  const bridgeId = await upsertKnowledge(bridgeText);
  labelById[bridgeId] = 'bridge-relevant';

  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: bridgeId,
    target_claim_id: seedId,
    link_type: 'related',
    confidence,
  });

  const bridgeEntity = await upsertEntity({
    id: `ent_bridge_${topK}_${fanout}_${confidence}`,
    type: 'Concept',
    name: 'Token Family',
    canonical_key: `token-family-${topK}-${fanout}-${confidence}`,
  });
  await linkClaimEntity(bridgeId, bridgeEntity.id);

  for (const [index, text] of noiseTexts.entries()) {
    const noiseId = await upsertKnowledge(text);
    labelById[noiseId] = `two-hop-noise-${index + 1}`;
    const noiseEntity = await upsertEntity({
      id: `ent_two_hop_noise_${topK}_${fanout}_${confidence}_${index}`,
      type: 'Artifact',
      name: `Facility Artifact ${index}`,
      canonical_key: `facility-artifact-${topK}-${fanout}-${confidence}-${index}`,
    });
    await linkClaimEntity(noiseId, noiseEntity.id);
    await upsertRelation({
      id: `rel_two_hop_noise_${topK}_${fanout}_${confidence}_${index}`,
      src_id: bridgeEntity.id,
      dst_id: noiseEntity.id,
      type: 'ASSOCIATED_WITH',
    });
  }

  const directCarryCount = Math.max(0, topK - 2);
  return {
    query: queryText,
    topK,
    relevantIds: [seedId, ...directIds.slice(1, 1 + directCarryCount), bridgeId],
    labelById,
    probeTopK: Math.max(topK + 4, 8),
  };
}

const SCENARIOS: ScenarioDefinition[] = [
  {
    name: 'forced graph presence replacement risk',
    description:
      'Regression guard: a noisy related claim must not replace a directly relevant lexical result when graph presence is fill-only.',
    seed: seedForcedPresenceNoiseScenario,
  },
  {
    name: 'generic hub entity bridge risk',
    description:
      'Regression guard: a generic entity hub must not bridge the seed to a noisy claim and replace a directly relevant lexical result.',
    seed: seedGenericHubNoiseScenario,
  },
  {
    name: 'confidence mitigated graph selection',
    description:
      'Regression guard: conservative graph presence should not worsen the ranked page even when confidence separates good and bad neighbors.',
    seed: seedConfidenceMitigatedScenario,
  },
];

const SWEEPS: SweepDefinition[] = [
  {
    name: 'related-star cliff sweep',
    description:
      'Sweeps top_k, related confidence, and fanout to confirm ensureClaimLinkPresence no longer displaces directly relevant hits.',
    cases: expandParameterGrid({
      top_k: [1, 2, 3, 5],
      confidence: [0.2, 0.5, 0.9],
      fanout: [1, 16],
    }).map((params) => ({
      params,
      seed: () => seedRelatedStarSweepCase(params),
    })),
  },
  {
    name: 'generic-hub fanout sweep',
    description:
      'Sweeps generic hub fanout and top_k to confirm noisy entity-bridge claims no longer overtake weak direct hits through forced insertion.',
    cases: expandParameterGrid({
      top_k: [3, 5, 10],
      fanout: [1, 8, 32],
    }).map((params) => ({
      params,
      seed: () => seedGenericHubSweepCase(params),
    })),
  },
  {
    name: 'two-hop contamination sweep',
    description:
      'Sweeps bridge confidence, fanout, and top_k to confirm downstream two-hop noise no longer reaches the ranked page through forced insertion.',
    cases: expandParameterGrid({
      top_k: [2, 3, 5],
      confidence: [0.2, 0.5, 0.9],
      fanout: [1, 32],
    }).map((params) => ({
      params,
      seed: () => seedTwoHopSweepCase(params),
    })),
  },
];

export async function runTopologyNoiseBenchmark(): Promise<TopologyNoiseBenchmarkReport> {
  return withRestoredEmbeddingService(async () => {
    const scenarios: TopologyNoiseScenarioReport[] = [];
    const sweeps: TopologyNoiseSweepReport[] = [];

    for (const definition of SCENARIOS) {
      const baseline = await runScenarioVariant(definition, false, ANCHOR_REPEATS);
      const naturalTopology = await runScenarioVariant(definition, true, ANCHOR_REPEATS, {
        disableGraphPresenceInjection: true,
      });
      const topology = await runScenarioVariant(definition, true, ANCHOR_REPEATS);
      const naturalDeltas = computeDeltas(baseline.metrics, naturalTopology.metrics);
      const deltas = computeDeltas(baseline.metrics, topology.metrics);
      const injectionDeltas = computeDeltas(naturalTopology.metrics, topology.metrics);

      scenarios.push({
        name: definition.name,
        description: definition.description,
        top_k: baseline.topK,
        relevant_labels: baseline.relevantLabels,
        baseline: baseline.metrics,
        natural_topology: naturalTopology.metrics,
        topology: topology.metrics,
        natural_deltas: naturalDeltas,
        deltas,
        injection_deltas: injectionDeltas,
        ...(topology.diagnostics ? { diagnostics: topology.diagnostics } : {}),
      });
    }

    for (const sweep of SWEEPS) {
      const cases: TopologyNoiseSweepCaseReport[] = [];
      for (const definition of sweep.cases) {
        const baseline = await runSweepCaseVariant(definition, false, SWEEP_REPEATS);
        const naturalTopology = await runSweepCaseVariant(definition, true, SWEEP_REPEATS, {
          disableGraphPresenceInjection: true,
        });
        const topology = await runSweepCaseVariant(definition, true, SWEEP_REPEATS);
        const naturalDeltas = computeDeltas(baseline.metrics, naturalTopology.metrics);
        const deltas = computeDeltas(baseline.metrics, topology.metrics);
        const injectionDeltas = computeDeltas(naturalTopology.metrics, topology.metrics);

        cases.push({
          params: definition.params,
          top_k: baseline.topK,
          relevant_labels: baseline.relevantLabels,
          baseline: baseline.metrics,
          natural_topology: naturalTopology.metrics,
          topology: topology.metrics,
          natural_deltas: naturalDeltas,
          deltas,
          injection_deltas: injectionDeltas,
          ...(topology.diagnostics ? { diagnostics: topology.diagnostics } : {}),
        });
      }

      sweeps.push({
        name: sweep.name,
        description: sweep.description,
        summary: summarizeSweepCases(cases),
        cases,
      });
    }

    const avg = (values: number[]): number =>
      Number(
        (values.reduce((sum, value) => sum + value, 0) / Math.max(values.length, 1)).toFixed(3)
      );
    const precisionDrops = scenarios
      .map((scenario) => Math.min(0, scenario.deltas.precision_at_k))
      .map((value) => Math.abs(value));
    const injectionPrecisionDrops = scenarios
      .map((scenario) => Math.min(0, scenario.injection_deltas.precision_at_k))
      .map((value) => Math.abs(value));
    const sweepCases = sweeps.flatMap((sweep) => sweep.cases);

    return {
      generated_at: new Date().toISOString(),
      environment: {
        node: process.version,
        platform: `${process.platform}/${process.arch}`,
      },
      summary: {
        scenario_count: scenarios.length,
        sweep_count: sweeps.length,
        sweep_case_count: sweepCases.length,
        precision_drop_scenarios: scenarios.filter((scenario) => scenario.deltas.precision_at_k < 0)
          .length,
        recall_drop_scenarios: scenarios.filter((scenario) => scenario.deltas.recall_at_k < 0)
          .length,
        increased_noise_scenarios: scenarios.filter((scenario) => scenario.deltas.noise_count > 0)
          .length,
        injection_worsened_scenarios: scenarios.filter(
          (scenario) => scenario.injection_deltas.precision_at_k < 0
        ).length,
        precision_drop_sweep_cases: sweepCases.filter(
          (caseReport) => caseReport.deltas.precision_at_k < 0
        ).length,
        recall_drop_sweep_cases: sweepCases.filter(
          (caseReport) => caseReport.deltas.recall_at_k < 0
        ).length,
        increased_noise_sweep_cases: sweepCases.filter(
          (caseReport) => caseReport.deltas.noise_count > 0
        ).length,
        injection_worsened_sweep_cases: sweepCases.filter(
          (caseReport) => caseReport.injection_deltas.precision_at_k < 0
        ).length,
        avg_precision_delta: avg(scenarios.map((scenario) => scenario.deltas.precision_at_k)),
        avg_recall_delta: avg(scenarios.map((scenario) => scenario.deltas.recall_at_k)),
        avg_latency_delta_ms: avg(scenarios.map((scenario) => scenario.deltas.avg_latency_ms)),
        avg_injection_precision_delta: avg(
          scenarios.map((scenario) => scenario.injection_deltas.precision_at_k)
        ),
        max_precision_drop: Number(Math.max(...precisionDrops, 0).toFixed(3)),
        max_sweep_precision_drop: Number(
          Math.max(...sweeps.map((sweep) => sweep.summary.max_precision_drop), 0).toFixed(3)
        ),
        max_injection_precision_drop: Number(Math.max(...injectionPrecisionDrops, 0).toFixed(3)),
      },
      scenarios,
      sweeps,
    };
  });
}

function formatParams(params: SweepCaseParams, keys: readonly string[]): string[] {
  return keys.map((key) => {
    const value = params[key];
    if (typeof value !== 'number') {
      return '';
    }
    return Number.isInteger(value) ? `${value}` : value.toFixed(2);
  });
}

export function generateTopologyNoiseBenchmarkMarkdown(
  report: TopologyNoiseBenchmarkReport
): string {
  const lines = [
    '# Topology Noise Benchmark',
    '',
    `Generated at: ${report.generated_at}`,
    `Environment: ${report.environment.node} on ${report.environment.platform}`,
    '',
    '## Summary',
    '',
    `- Anchor scenarios: ${report.summary.scenario_count}`,
    `- Sweep groups: ${report.summary.sweep_count}`,
    `- Sweep cases: ${report.summary.sweep_case_count}`,
    `- Precision-drop scenarios: ${report.summary.precision_drop_scenarios}`,
    `- Recall-drop scenarios: ${report.summary.recall_drop_scenarios}`,
    `- Increased-noise scenarios: ${report.summary.increased_noise_scenarios}`,
    `- Injection-worsened scenarios: ${report.summary.injection_worsened_scenarios}`,
    `- Precision-drop sweep cases: ${report.summary.precision_drop_sweep_cases}`,
    `- Recall-drop sweep cases: ${report.summary.recall_drop_sweep_cases}`,
    `- Increased-noise sweep cases: ${report.summary.increased_noise_sweep_cases}`,
    `- Injection-worsened sweep cases: ${report.summary.injection_worsened_sweep_cases}`,
    `- Average anchor precision delta: ${report.summary.avg_precision_delta.toFixed(3)}`,
    `- Average anchor recall delta: ${report.summary.avg_recall_delta.toFixed(3)}`,
    `- Average anchor latency delta (ms): ${report.summary.avg_latency_delta_ms.toFixed(3)}`,
    `- Average injection precision delta: ${report.summary.avg_injection_precision_delta.toFixed(3)}`,
    `- Max anchor precision drop: ${report.summary.max_precision_drop.toFixed(3)}`,
    `- Max sweep precision drop: ${report.summary.max_sweep_precision_drop.toFixed(3)}`,
    `- Max injection precision drop: ${report.summary.max_injection_precision_drop.toFixed(3)}`,
    '',
    '## Anchor Scenarios',
    '',
  ];

  for (const scenario of report.scenarios) {
    lines.push(`### ${scenario.name}`);
    lines.push('');
    lines.push(`- Description: ${scenario.description}`);
    lines.push(`- Relevant labels: ${scenario.relevant_labels.join(', ')}`);
    lines.push(
      `- Baseline top labels: ${scenario.baseline.top_claim_labels.join(', ') || '(none)'}`
    );
    lines.push(
      `- Natural topology top labels: ${scenario.natural_topology.top_claim_labels.join(', ') || '(none)'}`
    );
    lines.push(
      `- Topology top labels: ${scenario.topology.top_claim_labels.join(', ') || '(none)'}`
    );
    lines.push(`- Baseline noise labels: ${scenario.baseline.noise_labels.join(', ') || '(none)'}`);
    lines.push(
      `- Natural topology noise labels: ${scenario.natural_topology.noise_labels.join(', ') || '(none)'}`
    );
    lines.push(`- Topology noise labels: ${scenario.topology.noise_labels.join(', ') || '(none)'}`);
    lines.push(
      `- Precision@${scenario.top_k}: ${scenario.baseline.precision_at_k.toFixed(3)} -> ${scenario.topology.precision_at_k.toFixed(3)}`
    );
    lines.push(
      `- Natural precision@${scenario.top_k}: ${scenario.natural_topology.precision_at_k.toFixed(3)}`
    );
    lines.push(
      `- Recall@${scenario.top_k}: ${scenario.baseline.recall_at_k.toFixed(3)} -> ${scenario.topology.recall_at_k.toFixed(3)}`
    );
    lines.push(
      `- Natural recall@${scenario.top_k}: ${scenario.natural_topology.recall_at_k.toFixed(3)}`
    );
    lines.push(
      `- Graph source share@${scenario.top_k}: ${scenario.baseline.graph_source_share.toFixed(3)} -> ${scenario.topology.graph_source_share.toFixed(3)}`
    );
    lines.push(
      `- Natural graph source share@${scenario.top_k}: ${scenario.natural_topology.graph_source_share.toFixed(3)}`
    );
    lines.push(
      `- Injection precision delta@${scenario.top_k}: ${scenario.injection_deltas.precision_at_k.toFixed(3)}`
    );
    if (scenario.topology.graph_claim_details.length > 0) {
      lines.push(
        `- Topology graph details: ${scenario.topology.graph_claim_details
          .map(
            (detail) =>
              `${detail.label}[depth=${detail.depth ?? 'null'}; path=${detail.path_kinds.join('>') || 'none'}]`
          )
          .join(', ')}`
      );
    }
    if (scenario.topology.probe_graph_claim_details.length > 0) {
      lines.push(
        `- Topology probe graph details: ${scenario.topology.probe_graph_claim_details
          .map(
            (detail) =>
              `${detail.label}[depth=${detail.depth ?? 'null'}; path=${detail.path_kinds.join('>') || 'none'}]`
          )
          .join(', ')}`
      );
    }
    lines.push(
      `- Avg latency (ms): ${scenario.baseline.avg_latency_ms.toFixed(3)} -> ${scenario.topology.avg_latency_ms.toFixed(3)}`
    );
    if (scenario.diagnostics) {
      lines.push(`- Diagnostics: ${JSON.stringify(scenario.diagnostics)}`);
    }
    lines.push('');
  }

  lines.push('## Sweep Matrices');
  lines.push('');

  for (const sweep of report.sweeps) {
    const paramKeys = Object.keys(sweep.cases[0]?.params ?? {});
    lines.push(`### ${sweep.name}`);
    lines.push('');
    lines.push(`- Description: ${sweep.description}`);
    lines.push(`- Cases: ${sweep.summary.case_count}`);
    lines.push(`- Precision-drop cases: ${sweep.summary.precision_drop_cases}`);
    lines.push(`- Recall-drop cases: ${sweep.summary.recall_drop_cases}`);
    lines.push(`- Increased-noise cases: ${sweep.summary.increased_noise_cases}`);
    lines.push(`- Injection-worsened cases: ${sweep.summary.injection_worsened_cases}`);
    lines.push(`- Max precision drop: ${sweep.summary.max_precision_drop.toFixed(3)}`);
    lines.push(
      `- Max injection precision drop: ${sweep.summary.max_injection_precision_drop.toFixed(3)}`
    );
    lines.push(`- Max graph source share: ${sweep.summary.max_graph_source_share.toFixed(3)}`);
    lines.push('');
    lines.push(
      `| ${[
        ...paramKeys,
        'baseline_p',
        'natural_p',
        'topology_p',
        'delta_p',
        'inj_delta_p',
        'baseline_r',
        'natural_r',
        'topology_r',
        'delta_r',
        'noise_delta',
        'graph_share',
        'natural_graph_share',
        'graph_paths',
      ].join(' | ')} |`
    );
    lines.push(
      `| ${[
        ...paramKeys,
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
        '---',
      ].join(' | ')} |`
    );
    for (const caseReport of sweep.cases) {
      const pathSummary =
        caseReport.topology.probe_graph_claim_details
          .map(
            (detail) =>
              `${detail.label}:${detail.depth ?? 'null'}:${detail.path_kinds.join('>') || 'none'}`
          )
          .join(', ') || '(none)';
      const values = [
        ...formatParams(caseReport.params, paramKeys),
        caseReport.baseline.precision_at_k.toFixed(3),
        caseReport.natural_topology.precision_at_k.toFixed(3),
        caseReport.topology.precision_at_k.toFixed(3),
        caseReport.deltas.precision_at_k.toFixed(3),
        caseReport.injection_deltas.precision_at_k.toFixed(3),
        caseReport.baseline.recall_at_k.toFixed(3),
        caseReport.natural_topology.recall_at_k.toFixed(3),
        caseReport.topology.recall_at_k.toFixed(3),
        caseReport.deltas.recall_at_k.toFixed(3),
        `${caseReport.deltas.noise_count}`,
        caseReport.topology.graph_source_share.toFixed(3),
        caseReport.natural_topology.graph_source_share.toFixed(3),
        pathSummary,
      ];
      lines.push(`| ${values.join(' | ')} |`);
    }
    lines.push('');
  }

  return lines.join('\n');
}

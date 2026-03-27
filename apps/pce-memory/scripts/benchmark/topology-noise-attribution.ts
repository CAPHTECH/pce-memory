import { performance } from 'node:perf_hooks';
import { computeContentHash } from '@pce/embeddings';
import {
  CONNECTIVITY_SEED_MULTIPLIER,
  expandActivateResultsWithClaimLinks,
  getActivateExcludedWorkingStateStatuses,
  pageActivateResults,
  type ActivateSearchItem,
} from '../../src/core/handlers/shared.js';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection.js';
import { resetLayerScopeState } from '../../src/state/layerScopeState.js';
import { getRetrievalPolicy, resetMemoryState } from '../../src/state/memoryState.js';
import { linkClaimEntity, upsertEntity } from '../../src/store/entities.js';
import { setEmbeddingService, hybridSearchWithScores } from '../../src/store/hybridSearch.js';
import { initRateState, resetRates } from '../../src/store/rate.js';
import { upsertRelation } from '../../src/store/relations.js';
import { resolveTopologyConfig } from '../../src/store/search/types.js';
import {
  createBenchmarkEmbeddingService,
  withRestoredEmbeddingService,
} from './embeddingService.js';
import { dispatchToolOrThrow } from './toolResult.js';

interface ScenarioSeed {
  query: string;
  topK: number;
  relevantIds: string[];
  labelById: Record<string, string>;
  measurementRepeats?: number;
}

interface ScenarioDefinition {
  name: string;
  description: string;
  seed: () => Promise<ScenarioSeed>;
}

interface BenchmarkClaimInput {
  label: string;
  text: string;
  similarity: number;
}

interface TopologyPathEvidence {
  id: string;
  label: string;
  source: string;
  depth?: number;
  path_kinds: string[];
}

interface VariantMetrics {
  precision_at_k: number;
  recall_at_k: number;
  avg_latency_ms: number;
  top_claim_ids: string[];
  top_claim_labels: string[];
  noise_labels: string[];
  path_evidence: TopologyPathEvidence[];
}

interface VariantDelta {
  precision_at_k: number;
  recall_at_k: number;
  avg_latency_ms: number;
}

export interface TopologyNoiseAttributionScenarioReport {
  name: string;
  description: string;
  top_k: number;
  relevant_labels: string[];
  baseline: VariantMetrics;
  topology_natural: VariantMetrics;
  topology_injected: VariantMetrics;
  natural_noise_labels: string[];
  forced_noise_labels: string[];
  injected_only_path_evidence: TopologyPathEvidence[];
  deltas: {
    natural_vs_baseline: VariantDelta;
    injected_vs_baseline: VariantDelta;
    injected_vs_natural: VariantDelta;
  };
}

export interface TopologyNoiseAttributionReport {
  generated_at: string;
  environment: {
    node: string;
    platform: string;
  };
  summary: {
    scenario_count: number;
    injection_only_noise_scenarios: number;
    natural_noise_scenarios: number;
    avg_natural_precision_delta: number;
    avg_injected_precision_delta: number;
    max_natural_precision_drop: number;
    max_injected_precision_drop: number;
  };
  scenarios: TopologyNoiseAttributionScenarioReport[];
}

const RELATED_QUERY = 'issuer rotation partner access';
const HUB_QUERY = 'oauth issuer validation mobile auth service';
const TWO_HOP_QUERY = 'session revocation device theft replay defense';

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createSimilarityVector(similarity: number): readonly number[] {
  const clamped = Math.max(-0.999999, Math.min(0.999999, similarity));
  return normalize([clamped, Math.sqrt(Math.max(0, 1 - clamped * clamped))]);
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

async function createBenchmarkClaims(input: {
  queryText: string;
  claims: readonly BenchmarkClaimInput[];
}): Promise<{ idsByLabel: Record<string, string>; labelById: Record<string, string> }> {
  const embeddings: Record<string, readonly number[]> = {
    [input.queryText]: normalize([1, 0]),
  };
  for (const claim of input.claims) {
    embeddings[claim.text] = createSimilarityVector(claim.similarity);
  }
  setEmbeddingService(
    createBenchmarkEmbeddingService(embeddings, {
      fallbackEmbedding: normalize([-1, 0]),
      modelVersion: 'topology-noise-attribution-v1',
    })
  );

  const idsByLabel: Record<string, string> = {};
  const labelById: Record<string, string> = {};
  for (const claim of input.claims) {
    const id = await upsertKnowledge(claim.text);
    idsByLabel[claim.label] = id;
    labelById[id] = claim.label;
  }

  return { idsByLabel, labelById };
}

function buildSearchConfig() {
  const hybridPolicy = getRetrievalPolicy().hybrid ?? {};
  const topologyConfig = resolveTopologyConfig(hybridPolicy.topology);
  return {
    searchConfig: {
      boundaryClasses: ['internal'],
      includeBreakdown: true,
      excludedWorkingStateStatuses: getActivateExcludedWorkingStateStatuses(false),
      ...(typeof hybridPolicy.alpha === 'number' ? { alpha: hybridPolicy.alpha } : {}),
      ...(typeof hybridPolicy.threshold === 'number' ? { threshold: hybridPolicy.threshold } : {}),
      ...(typeof hybridPolicy.k_txt === 'number' ? { kText: hybridPolicy.k_txt } : {}),
      ...(typeof hybridPolicy.k_vec === 'number' ? { kVec: hybridPolicy.k_vec } : {}),
      ...(topologyConfig ? { topology: topologyConfig } : {}),
    },
    topologyConfig,
  };
}

async function runInternalActivate(
  query: string,
  topK: number,
  disableGraphPresenceInjection: boolean,
  repeats: number = 1
): Promise<{ items: ActivateSearchItem[]; avgLatencyMs: number }> {
  const runOnce = async (): Promise<ActivateSearchItem[]> => {
    const { searchConfig, topologyConfig } = buildSearchConfig();
    const directCandidateLimit = Math.max(
      topK + 1,
      topK * CONNECTIVITY_SEED_MULTIPLIER,
      (topologyConfig?.seedK ?? 0) * CONNECTIVITY_SEED_MULTIPLIER
    );
    const durableResults = await hybridSearchWithScores(
      ['project'],
      directCandidateLimit,
      query,
      searchConfig
    );
    const expandedDurableResults = await expandActivateResultsWithClaimLinks(
      durableResults.map((item) => ({ ...item, source: 'search' as const })),
      {
        scopes: ['project'],
        boundaryClasses: ['internal'],
        excludedWorkingStateStatuses: getActivateExcludedWorkingStateStatuses(false),
        ...(topologyConfig ? { topology: topologyConfig } : {}),
      }
    );
    return pageActivateResults({
      results: expandedDurableResults,
      topK,
      disableGraphPresenceInjection,
    }).searchResults;
  };

  const startedAt = performance.now();
  const first = await runOnce();
  const samples = [performance.now() - startedAt];
  for (let index = 0; index < repeats; index++) {
    const repeatStartedAt = performance.now();
    await runOnce();
    samples.push(performance.now() - repeatStartedAt);
  }

  return {
    items: first,
    avgLatencyMs: samples.reduce((sum, value) => sum + value, 0) / Math.max(samples.length, 1),
  };
}

function measureVariant(
  items: ActivateSearchItem[],
  relevantIds: readonly string[],
  labelById: Record<string, string>,
  topK: number
): VariantMetrics {
  const top = items.slice(0, topK);
  const relevant = new Set(relevantIds);
  const matched = top.filter((item) => relevant.has(item.claim.id));

  return {
    precision_at_k: matched.length / topK,
    recall_at_k: relevant.size === 0 ? 0 : matched.length / relevant.size,
    avg_latency_ms: 0,
    top_claim_ids: top.map((item) => item.claim.id),
    top_claim_labels: top.map((item) => labelById[item.claim.id] ?? item.claim.id),
    noise_labels: top
      .filter((item) => !relevant.has(item.claim.id))
      .map((item) => labelById[item.claim.id] ?? item.claim.id),
    path_evidence: top
      .filter((item) => item.topology !== undefined)
      .map((item) => ({
        id: item.claim.id,
        label: labelById[item.claim.id] ?? item.claim.id,
        source: item.source ?? 'search',
        depth: item.topology?.depth,
        path_kinds: (item.topology?.path ?? []).map((segment) => segment.kind),
      })),
  };
}

function buildDelta(left: VariantMetrics, right: VariantMetrics): VariantDelta {
  return {
    precision_at_k: Number((right.precision_at_k - left.precision_at_k).toFixed(3)),
    recall_at_k: Number((right.recall_at_k - left.recall_at_k).toFixed(3)),
    avg_latency_ms: Number((right.avg_latency_ms - left.avg_latency_ms).toFixed(3)),
  };
}

function avg(values: number[]): number {
  return Number(
    (values.reduce((sum, value) => sum + value, 0) / Math.max(values.length, 1)).toFixed(3)
  );
}

async function runScenario(
  definition: ScenarioDefinition
): Promise<TopologyNoiseAttributionScenarioReport> {
  await resetBenchmarkState();
  await applyPolicy(false);
  const seededBaseline = await definition.seed();
  const baselineRun = await runInternalActivate(
    seededBaseline.query,
    seededBaseline.topK,
    true,
    seededBaseline.measurementRepeats ?? 1
  );
  const baseline = measureVariant(
    baselineRun.items,
    seededBaseline.relevantIds,
    seededBaseline.labelById,
    seededBaseline.topK
  );
  baseline.avg_latency_ms = Number(baselineRun.avgLatencyMs.toFixed(3));

  await resetBenchmarkState();
  await applyPolicy(true);
  const seededNatural = await definition.seed();
  const naturalRun = await runInternalActivate(
    seededNatural.query,
    seededNatural.topK,
    true,
    seededNatural.measurementRepeats ?? 1
  );
  const topologyNatural = measureVariant(
    naturalRun.items,
    seededNatural.relevantIds,
    seededNatural.labelById,
    seededNatural.topK
  );
  topologyNatural.avg_latency_ms = Number(naturalRun.avgLatencyMs.toFixed(3));

  await resetBenchmarkState();
  await applyPolicy(true);
  const seededInjected = await definition.seed();
  const injectedRun = await runInternalActivate(
    seededInjected.query,
    seededInjected.topK,
    false,
    seededInjected.measurementRepeats ?? 1
  );
  const topologyInjected = measureVariant(
    injectedRun.items,
    seededInjected.relevantIds,
    seededInjected.labelById,
    seededInjected.topK
  );
  topologyInjected.avg_latency_ms = Number(injectedRun.avgLatencyMs.toFixed(3));

  const naturalIds = new Set(topologyNatural.top_claim_ids);
  const relevantIds = new Set(seededInjected.relevantIds);
  const forcedNoiseLabels = topologyInjected.top_claim_ids
    .filter((id) => !naturalIds.has(id) && !relevantIds.has(id))
    .map((id) => seededInjected.labelById[id] ?? id);
  const forcedNoiseLabelsSet = new Set(forcedNoiseLabels);
  const injectedOnlyPathEvidence = topologyInjected.path_evidence.filter((evidence) =>
    forcedNoiseLabelsSet.has(evidence.label)
  );

  return {
    name: definition.name,
    description: definition.description,
    top_k: seededInjected.topK,
    relevant_labels: seededInjected.relevantIds.map((id) => seededInjected.labelById[id] ?? id),
    baseline,
    topology_natural: topologyNatural,
    topology_injected: topologyInjected,
    natural_noise_labels: topologyNatural.noise_labels,
    forced_noise_labels: forcedNoiseLabels,
    injected_only_path_evidence: injectedOnlyPathEvidence,
    deltas: {
      natural_vs_baseline: buildDelta(baseline, topologyNatural),
      injected_vs_baseline: buildDelta(baseline, topologyInjected),
      injected_vs_natural: buildDelta(topologyNatural, topologyInjected),
    },
  };
}

async function seedRelatedInjectionScenario(): Promise<ScenarioSeed> {
  const { idsByLabel, labelById } = await createBenchmarkClaims({
    queryText: RELATED_QUERY,
    claims: [
      {
        label: 'seed',
        text: 'Issuer rotation anchor for partner access policy.',
        similarity: 0.995,
      },
      {
        label: 'direct-relevant',
        text: 'Partner issuer rotation playbook for access rollout.',
        similarity: 0.92,
      },
      {
        label: 'related-noise-1',
        text: 'Quarterly catering schedule for regional office seating.',
        similarity: -0.1,
      },
    ],
  });

  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: idsByLabel['related-noise-1'],
    target_claim_id: idsByLabel['seed'],
    link_type: 'related',
    confidence: 0.9,
  });

  return {
    query: RELATED_QUERY,
    topK: 2,
    relevantIds: [idsByLabel['seed'], idsByLabel['direct-relevant']],
    labelById,
  };
}

async function seedHubInjectionScenario(): Promise<ScenarioSeed> {
  const { idsByLabel, labelById } = await createBenchmarkClaims({
    queryText: HUB_QUERY,
    claims: [
      {
        label: 'seed',
        text: 'OAuth issuer validation anchor for mobile auth service.',
        similarity: 0.995,
      },
      {
        label: 'direct-relevant-1',
        text: 'OAuth issuer validation deployment guide for mobile auth service.',
        similarity: 0.95,
      },
      {
        label: 'direct-relevant-2',
        text: 'Mobile auth service issuer validation runbook.',
        similarity: 0.84,
      },
      {
        label: 'hub-noise-1',
        text: 'Poster sponsorship budget and catering vendor checklist.',
        similarity: -0.1,
      },
    ],
  });

  const genericHub = await upsertEntity({
    id: 'ent_attribution_general_hub',
    type: 'Concept',
    name: 'General',
    canonical_key: 'general-attribution',
  });
  const noiseBucket = await upsertEntity({
    id: 'ent_attribution_hub_bucket',
    type: 'Artifact',
    name: 'Campaign Hub',
    canonical_key: 'campaign-hub-attribution',
  });

  await linkClaimEntity(idsByLabel['seed'], genericHub.id);
  await linkClaimEntity(idsByLabel['hub-noise-1'], noiseBucket.id);
  await upsertRelation({
    id: 'rel_attribution_general_to_campaign',
    src_id: genericHub.id,
    dst_id: noiseBucket.id,
    type: 'ASSOCIATED_WITH',
  });

  return {
    query: HUB_QUERY,
    topK: 3,
    relevantIds: [
      idsByLabel['seed'],
      idsByLabel['direct-relevant-1'],
      idsByLabel['direct-relevant-2'],
    ],
    labelById,
  };
}

async function seedTwoHopInjectionScenario(): Promise<ScenarioSeed> {
  const { idsByLabel, labelById } = await createBenchmarkClaims({
    queryText: TWO_HOP_QUERY,
    claims: [
      {
        label: 'seed',
        text: 'Session revocation anchor for device theft replay defense.',
        similarity: 0.995,
      },
      {
        label: 'direct-relevant-1',
        text: 'Session revocation rollout for device theft response.',
        similarity: 0.82,
      },
      {
        label: 'relevant-bridge',
        text: 'Refresh token family revocation prevents replay after device theft.',
        similarity: 0.68,
      },
      {
        label: 'two-hop-noise-1',
        text: 'Facilities keycard replacement for office visitors.',
        similarity: -0.1,
      },
    ],
  });

  await dispatchToolOrThrow('pce_memory_link_claims', {
    source_claim_id: idsByLabel['relevant-bridge'],
    target_claim_id: idsByLabel['seed'],
    link_type: 'related',
    confidence: 0.9,
  });

  const bridgeEntity = await upsertEntity({
    id: 'ent_attribution_two_hop_bridge',
    type: 'Concept',
    name: 'Revocation Family',
    canonical_key: 'revocation-family-attribution',
  });
  const noiseBucket = await upsertEntity({
    id: 'ent_attribution_two_hop_bucket',
    type: 'Artifact',
    name: 'Facility Bucket',
    canonical_key: 'facility-bucket-attribution',
  });

  await linkClaimEntity(idsByLabel['relevant-bridge'], bridgeEntity.id);
  await linkClaimEntity(idsByLabel['two-hop-noise-1'], noiseBucket.id);
  await upsertRelation({
    id: 'rel_attribution_two_hop',
    src_id: bridgeEntity.id,
    dst_id: noiseBucket.id,
    type: 'ASSOCIATED_WITH',
  });

  return {
    query: TWO_HOP_QUERY,
    topK: 3,
    relevantIds: [
      idsByLabel['seed'],
      idsByLabel['direct-relevant-1'],
      idsByLabel['relevant-bridge'],
    ],
    labelById,
  };
}

const SCENARIOS: readonly ScenarioDefinition[] = [
  {
    name: 'related injection attribution',
    description:
      'Regression guard comparing baseline, natural topology, and injected topology for a direct claim_link contamination case.',
    seed: seedRelatedInjectionScenario,
  },
  {
    name: 'hub injection attribution',
    description:
      'Regression guard comparing baseline, natural topology, and injected topology for a generic entity bridge contamination case.',
    seed: seedHubInjectionScenario,
  },
  {
    name: 'two-hop path attribution',
    description:
      'Regression guard for a two-hop claim_link -> entity_relation contamination case under the current multi-seed activate pipeline.',
    seed: seedTwoHopInjectionScenario,
  },
];

export async function runTopologyNoiseAttributionBenchmark(): Promise<TopologyNoiseAttributionReport> {
  return withRestoredEmbeddingService(async () => {
    const scenarios: TopologyNoiseAttributionScenarioReport[] = [];
    for (const scenario of SCENARIOS) {
      scenarios.push(await runScenario(scenario));
    }

    const naturalPrecisionDrops = scenarios
      .map((scenario) => Math.min(0, scenario.deltas.natural_vs_baseline.precision_at_k))
      .map((value) => Math.abs(value));
    const injectedPrecisionDrops = scenarios
      .map((scenario) => Math.min(0, scenario.deltas.injected_vs_baseline.precision_at_k))
      .map((value) => Math.abs(value));

    return {
      generated_at: new Date().toISOString(),
      environment: {
        node: process.version,
        platform: `${process.platform}/${process.arch}`,
      },
      summary: {
        scenario_count: scenarios.length,
        injection_only_noise_scenarios: scenarios.filter(
          (scenario) => scenario.forced_noise_labels.length > 0
        ).length,
        natural_noise_scenarios: scenarios.filter(
          (scenario) => scenario.natural_noise_labels.length > 0
        ).length,
        avg_natural_precision_delta: avg(
          scenarios.map((scenario) => scenario.deltas.natural_vs_baseline.precision_at_k)
        ),
        avg_injected_precision_delta: avg(
          scenarios.map((scenario) => scenario.deltas.injected_vs_baseline.precision_at_k)
        ),
        max_natural_precision_drop: Number(Math.max(...naturalPrecisionDrops, 0).toFixed(3)),
        max_injected_precision_drop: Number(Math.max(...injectedPrecisionDrops, 0).toFixed(3)),
      },
      scenarios,
    };
  });
}

function formatPathEvidence(evidence: TopologyPathEvidence): string {
  const depth = evidence.depth ?? '?';
  const pathKinds = evidence.path_kinds.length > 0 ? evidence.path_kinds.join('>') : '(none)';
  return `${evidence.label}[source=${evidence.source}; depth=${depth}; path=${pathKinds}]`;
}

export function generateTopologyNoiseAttributionMarkdown(
  report: TopologyNoiseAttributionReport
): string {
  const lines = [
    '# Topology Noise Attribution Benchmark',
    '',
    `Generated at: ${report.generated_at}`,
    `Environment: ${report.environment.node} on ${report.environment.platform}`,
    '',
    '## Summary',
    '',
    `- Scenarios: ${report.summary.scenario_count}`,
    `- Injection-only noise scenarios: ${report.summary.injection_only_noise_scenarios}`,
    `- Natural-noise scenarios: ${report.summary.natural_noise_scenarios}`,
    `- Average natural precision delta: ${report.summary.avg_natural_precision_delta.toFixed(3)}`,
    `- Average injected precision delta: ${report.summary.avg_injected_precision_delta.toFixed(3)}`,
    `- Max natural precision drop: ${report.summary.max_natural_precision_drop.toFixed(3)}`,
    `- Max injected precision drop: ${report.summary.max_injected_precision_drop.toFixed(3)}`,
    '',
    '## Scenarios',
    '',
  ];

  for (const scenario of report.scenarios) {
    lines.push(`### ${scenario.name}`);
    lines.push('');
    lines.push(`- Description: ${scenario.description}`);
    lines.push(`- Relevant labels: ${scenario.relevant_labels.join(', ')}`);
    lines.push(`- Baseline top labels: ${scenario.baseline.top_claim_labels.join(', ')}`);
    lines.push(
      `- Natural topology top labels: ${scenario.topology_natural.top_claim_labels.join(', ')}`
    );
    lines.push(
      `- Injected topology top labels: ${scenario.topology_injected.top_claim_labels.join(', ')}`
    );
    lines.push(`- Natural noise labels: ${scenario.natural_noise_labels.join(', ') || '(none)'}`);
    lines.push(`- Forced noise labels: ${scenario.forced_noise_labels.join(', ') || '(none)'}`);
    lines.push(
      `- Natural precision@${scenario.top_k}: ${scenario.baseline.precision_at_k.toFixed(3)} -> ${scenario.topology_natural.precision_at_k.toFixed(3)}`
    );
    lines.push(
      `- Injected precision@${scenario.top_k}: ${scenario.baseline.precision_at_k.toFixed(3)} -> ${scenario.topology_injected.precision_at_k.toFixed(3)}`
    );
    lines.push(
      `- Injected-only path evidence: ${
        scenario.injected_only_path_evidence.map(formatPathEvidence).join(', ') || '(none)'
      }`
    );
    lines.push('');
  }

  return lines.join('\n');
}

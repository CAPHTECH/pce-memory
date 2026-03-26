import { performance } from 'node:perf_hooks';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../../src/core/handlers.js';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection.js';
import { resetLayerScopeState } from '../../src/state/layerScopeState.js';
import { resetMemoryState } from '../../src/state/memoryState.js';
import { linkClaimEntity, upsertEntity } from '../../src/store/entities.js';
import { setEmbeddingService } from '../../src/store/hybridSearch.js';
import { initRateState, resetRates } from '../../src/store/rate.js';
import { upsertRelation } from '../../src/store/relations.js';

interface ActivateClaimResult {
  claim: { id: string };
  source?: string;
}

interface ScenarioSeed {
  query: string;
  topK: number;
  relevantIds: string[];
  labelById: Record<string, string>;
}

interface ScenarioDefinition {
  name: string;
  description: string;
  pathKind: 'claim_link' | 'entity_relation' | 'supersession';
  seed: () => Promise<ScenarioSeed>;
}

interface VariantMetrics {
  precision_at_k: number;
  recall_at_k: number;
  avg_latency_ms: number;
  result_count: number;
  top_claim_ids: string[];
  top_claim_labels: string[];
  top_claim_sources: string[];
}

export interface TopologyScenarioReport {
  name: string;
  description: string;
  path_kind: 'claim_link' | 'entity_relation' | 'supersession';
  top_k: number;
  relevant_labels: string[];
  baseline: VariantMetrics;
  topology: VariantMetrics;
  deltas: {
    precision_at_k: number;
    recall_at_k: number;
    avg_latency_ms: number;
  };
}

export interface TopologyBenchmarkReport {
  generated_at: string;
  environment: {
    node: string;
    platform: string;
  };
  summary: {
    scenario_count: number;
    improved_precision_scenarios: number;
    improved_recall_scenarios: number;
    avg_precision_delta: number;
    avg_recall_delta: number;
    avg_latency_delta_ms: number;
  };
  scenarios: TopologyScenarioReport[];
}

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createEmbeddingService(embeddings: Record<string, readonly number[]>): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      async () =>
        E.right({
          embedding: embeddings[text] ?? normalize([-1, 0]),
          modelVersion: 'topology-benchmark-v1',
        }),
  };
}

async function resetBenchmarkState(): Promise<void> {
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
  await dispatchTool('pce_memory_policy_apply', { yaml: buildPolicyYaml(topologyEnabled) });
}

async function upsertKnowledge(text: string): Promise<string> {
  const result = await dispatchTool('pce_memory_upsert', {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'benchmark' },
  });
  return result.structuredContent!.id as string;
}

async function runMeasuredActivate(
  query: string,
  topK: number,
  repeats: number = 8
): Promise<{ claims: ActivateClaimResult[]; avgLatencyMs: number }> {
  const first = (await dispatchTool('pce_memory_activate', {
    scope: ['project'],
    allow: ['answer:task'],
    q: query,
    top_k: topK,
  }).then((result) => result.structuredContent)) as {
    claims: ActivateClaimResult[];
  };

  const samples: number[] = [];
  for (let index = 0; index < repeats; index++) {
    const startedAt = performance.now();
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: query,
      top_k: topK,
    });
    samples.push(performance.now() - startedAt);
  }

  return {
    claims: first.claims,
    avgLatencyMs: samples.reduce((sum, value) => sum + value, 0) / Math.max(samples.length, 1),
  };
}

function measureActivateTopK(
  claims: ActivateClaimResult[],
  relevantIds: readonly string[],
  labelById: Record<string, string>,
  k: number
): VariantMetrics {
  const top = claims.slice(0, k);
  const relevant = new Set(relevantIds);
  const matched = top.filter((item) => relevant.has(item.claim.id));

  return {
    precision_at_k: matched.length / k,
    recall_at_k: relevant.size === 0 ? 0 : matched.length / relevant.size,
    avg_latency_ms: 0,
    result_count: claims.length,
    top_claim_ids: top.map((item) => item.claim.id),
    top_claim_labels: top.map((item) => labelById[item.claim.id] ?? item.claim.id),
    top_claim_sources: top.map((item) => item.source ?? 'search'),
  };
}

async function runScenarioVariant(
  definition: ScenarioDefinition,
  topologyEnabled: boolean
): Promise<{ metrics: VariantMetrics; topK: number; relevantLabels: string[] }> {
  await resetBenchmarkState();
  await applyPolicy(topologyEnabled);
  const seeded = await definition.seed();
  const measured = await runMeasuredActivate(seeded.query, seeded.topK);
  const metrics = measureActivateTopK(
    measured.claims,
    seeded.relevantIds,
    seeded.labelById,
    seeded.topK
  );
  metrics.avg_latency_ms = Number(measured.avgLatencyMs.toFixed(3));
  return {
    metrics,
    topK: seeded.topK,
    relevantLabels: seeded.relevantIds.map((id) => seeded.labelById[id] ?? id),
  };
}

async function seedClaimLinkScenario(): Promise<ScenarioSeed> {
  const anchorText =
    'Connectivity anchor: maple login tokens require issuer validation and short session expiry.';
  const relatedText =
    'Connectivity extension: orchard renewal ledgers extend maple access controls with revocation windows.';
  const distractorText =
    'Connectivity distractor: maple login token onboarding checklist for support handoff.';
  const queryText = 'maple login token issuer validation handoff';

  setEmbeddingService(
    createEmbeddingService({
      [anchorText]: normalize([1, 0]),
      [relatedText]: normalize([0.6, 0.8]),
      [distractorText]: normalize([1, 1]),
      [queryText]: normalize([1, -1]),
    })
  );

  const anchorId = await upsertKnowledge(anchorText);
  const relatedId = await upsertKnowledge(relatedText);
  const distractorId = await upsertKnowledge(distractorText);

  await dispatchTool('pce_memory_link_claims', {
    source_claim_id: relatedId,
    target_claim_id: anchorId,
    link_type: 'related',
  });

  return {
    query: queryText,
    topK: 3,
    relevantIds: [anchorId, relatedId],
    labelById: {
      [anchorId]: 'anchor',
      [relatedId]: 'related',
      [distractorId]: 'distractor',
    },
  };
}

async function seedEntityRelationScenario(): Promise<ScenarioSeed> {
  const seedText = 'OAuth issuer validation requires strict audience checks and nonce binding.';
  const bridgedText = 'Refresh token family revocation ledger stops replay after device theft.';
  const distractorText = 'OAuth launch checklist covers banner copy and stakeholder scheduling.';
  const queryText = 'oauth issuer validation audience checks';

  setEmbeddingService(
    createEmbeddingService({
      [seedText]: normalize([1, 0]),
      [bridgedText]: normalize([-1, 0]),
      [distractorText]: normalize([0.8, 0.2]),
      [queryText]: normalize([1, 0]),
    })
  );

  const seedId = await upsertKnowledge(seedText);
  const bridgedId = await upsertKnowledge(bridgedText);
  const distractorId = await upsertKnowledge(distractorText);

  const serviceEntity = await upsertEntity({
    id: 'ent_bench_auth_service',
    type: 'Artifact',
    name: 'Auth Service',
    canonical_key: 'auth-service',
  });
  const ledgerEntity = await upsertEntity({
    id: 'ent_bench_revocation_ledger',
    type: 'Artifact',
    name: 'Revocation Ledger',
    canonical_key: 'revocation-ledger',
  });

  await linkClaimEntity(seedId, serviceEntity.id);
  await linkClaimEntity(bridgedId, ledgerEntity.id);
  await upsertRelation({
    id: 'rel_bench_service_to_ledger',
    src_id: serviceEntity.id,
    dst_id: ledgerEntity.id,
    type: 'DEPENDS_ON',
  });

  return {
    query: queryText,
    topK: 3,
    relevantIds: [seedId, bridgedId],
    labelById: {
      [seedId]: 'seed',
      [bridgedId]: 'entity-bridged',
      [distractorId]: 'distractor',
    },
  };
}

async function seedSupersessionScenario(): Promise<ScenarioSeed> {
  const oldText = 'Legacy issuer validation runbook version one applies static partner secrets.';
  const newText =
    'Replacement issuer validation runbook version two rotates partner secrets hourly.';
  const distractorText =
    'Cafeteria seating plan and office badge checklist for facilities coordination.';
  const queryText = 'legacy issuer validation static partner secrets';

  setEmbeddingService(
    createEmbeddingService({
      [oldText]: normalize([1, 0]),
      [newText]: normalize([-1, 0]),
      [distractorText]: normalize([0, 1]),
      [queryText]: normalize([1, 0]),
    })
  );

  const oldId = await upsertKnowledge(oldText);
  const newId = await upsertKnowledge(newText);
  const distractorId = await upsertKnowledge(distractorText);

  await dispatchTool('pce_memory_link_claims', {
    source_claim_id: newId,
    target_claim_id: oldId,
    link_type: 'supersedes',
  });

  return {
    query: queryText,
    topK: 1,
    relevantIds: [newId],
    labelById: {
      [oldId]: 'superseded-old',
      [newId]: 'replacement-new',
      [distractorId]: 'distractor',
    },
  };
}

const SCENARIOS: ScenarioDefinition[] = [
  {
    name: 'claim-link recall',
    description:
      'Recover a semantically related claim that is only reachable through explicit claim links.',
    pathKind: 'claim_link',
    seed: seedClaimLinkScenario,
  },
  {
    name: 'entity-bridge recall',
    description:
      'Recover a relevant claim through claim -> entity -> relation -> entity -> claim traversal.',
    pathKind: 'entity_relation',
    seed: seedEntityRelationScenario,
  },
  {
    name: 'supersession refresh',
    description:
      'Replace a stale directly matched claim with the superseding claim when topology is enabled.',
    pathKind: 'supersession',
    seed: seedSupersessionScenario,
  },
];

export async function runTopologyEffectivenessBenchmark(): Promise<TopologyBenchmarkReport> {
  const scenarios: TopologyScenarioReport[] = [];

  for (const definition of SCENARIOS) {
    const baseline = await runScenarioVariant(definition, false);
    const topology = await runScenarioVariant(definition, true);

    scenarios.push({
      name: definition.name,
      description: definition.description,
      path_kind: definition.pathKind,
      top_k: baseline.topK,
      relevant_labels: baseline.relevantLabels,
      baseline: baseline.metrics,
      topology: topology.metrics,
      deltas: {
        precision_at_k: Number(
          (topology.metrics.precision_at_k - baseline.metrics.precision_at_k).toFixed(3)
        ),
        recall_at_k: Number(
          (topology.metrics.recall_at_k - baseline.metrics.recall_at_k).toFixed(3)
        ),
        avg_latency_ms: Number(
          (topology.metrics.avg_latency_ms - baseline.metrics.avg_latency_ms).toFixed(3)
        ),
      },
    });
  }

  const avg = (values: number[]): number =>
    Number((values.reduce((sum, value) => sum + value, 0) / Math.max(values.length, 1)).toFixed(3));

  return {
    generated_at: new Date().toISOString(),
    environment: {
      node: process.version,
      platform: `${process.platform}/${process.arch}`,
    },
    summary: {
      scenario_count: scenarios.length,
      improved_precision_scenarios: scenarios.filter(
        (scenario) => scenario.deltas.precision_at_k > 0
      ).length,
      improved_recall_scenarios: scenarios.filter((scenario) => scenario.deltas.recall_at_k > 0)
        .length,
      avg_precision_delta: avg(scenarios.map((scenario) => scenario.deltas.precision_at_k)),
      avg_recall_delta: avg(scenarios.map((scenario) => scenario.deltas.recall_at_k)),
      avg_latency_delta_ms: avg(scenarios.map((scenario) => scenario.deltas.avg_latency_ms)),
    },
    scenarios,
  };
}

export function generateTopologyBenchmarkMarkdown(report: TopologyBenchmarkReport): string {
  const lines = [
    '# Topology Effectiveness Benchmark',
    '',
    `Generated at: ${report.generated_at}`,
    `Environment: ${report.environment.node} on ${report.environment.platform}`,
    '',
    '## Summary',
    '',
    `- Scenarios: ${report.summary.scenario_count}`,
    `- Improved precision scenarios: ${report.summary.improved_precision_scenarios}`,
    `- Improved recall scenarios: ${report.summary.improved_recall_scenarios}`,
    `- Average precision delta: ${report.summary.avg_precision_delta.toFixed(3)}`,
    `- Average recall delta: ${report.summary.avg_recall_delta.toFixed(3)}`,
    `- Average latency delta (ms): ${report.summary.avg_latency_delta_ms.toFixed(3)}`,
    '',
    '## Scenarios',
    '',
  ];

  for (const scenario of report.scenarios) {
    lines.push(`### ${scenario.name}`);
    lines.push('');
    lines.push(`- Path kind: ${scenario.path_kind}`);
    lines.push(`- Description: ${scenario.description}`);
    lines.push(`- Relevant labels: ${scenario.relevant_labels.join(', ')}`);
    lines.push(
      `- Baseline top labels: ${scenario.baseline.top_claim_labels.join(', ') || '(none)'}`
    );
    lines.push(
      `- Topology top labels: ${scenario.topology.top_claim_labels.join(', ') || '(none)'}`
    );
    lines.push(
      `- Precision@${scenario.top_k}: ${scenario.baseline.precision_at_k.toFixed(3)} -> ${scenario.topology.precision_at_k.toFixed(3)}`
    );
    lines.push(
      `- Recall@${scenario.top_k}: ${scenario.baseline.recall_at_k.toFixed(3)} -> ${scenario.topology.recall_at_k.toFixed(3)}`
    );
    lines.push(
      `- Avg latency (ms): ${scenario.baseline.avg_latency_ms.toFixed(3)} -> ${scenario.topology.avg_latency_ms.toFixed(3)}`
    );
    lines.push('');
  }

  return lines.join('\n');
}

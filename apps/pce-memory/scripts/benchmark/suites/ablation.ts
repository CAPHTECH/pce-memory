/**
 * Ablation study: measure the contribution of each search component.
 *
 * Configs: text-only, vector-only, hybrid-no-rerank, hybrid-baseline, hybrid-mmr, hybrid-intent.
 */

import { performance } from 'node:perf_hooks';
import { evaluateRetrieval } from '../../../external/assay-kit/packages/assay-kit/src/metrics/combined.ts';
import { loadDataset } from '../../../external/assay-kit/packages/assay-kit/src/dataset/loader.ts';
import { TEST_CLAIMS } from '../../assay/test-data.ts';
import { initDb, initSchema, resetDbAsync } from '../../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
import type { ClaimKind } from '../../../src/domain/types';
import { generateClaims } from '../data/synthetic-claims';
import type {
  AblationConfig,
  AblationConfigResult,
  AblationDelta,
  AblationResult,
  RerankAblationResult,
  QueryMetrics,
} from '../types';

const TIMESTAMP_INTERVAL_MS = 10;
const BASELINE_NAME = 'hybrid-baseline';

// NOTE: resolveCandidateLimit() in hybridSearch.ts treats 0 as invalid (falls back to default).
// We use alpha=0/1 to zero-weight the unwanted signal, and keep kText/kVec at minimum (1)
// so the SQL query runs but the score contribution is zeroed by alpha.
export const ABLATION_CONFIGS: AblationConfig[] = [
  {
    name: 'text-only',
    alpha: 0.0,
    kText: 128,
    kVec: 1,
    enableRerank: false,
    mmr: { enabled: false },
  },
  {
    name: 'vector-only',
    alpha: 1.0,
    kText: 1,
    kVec: 256,
    enableRerank: false,
    mmr: { enabled: false },
  },
  {
    name: 'hybrid-no-rerank',
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: false,
    mmr: { enabled: false },
  },
  {
    name: BASELINE_NAME,
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: true,
    mmr: { enabled: false },
  },
  {
    name: 'hybrid-mmr',
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: true,
    mmr: { enabled: true, lambda: 0.72 },
  },
  {
    name: 'hybrid-intent',
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: true,
    mmr: { enabled: false },
    intent: 'design_decision',
  },
];

type QueryType = {
  id: string;
  text: string;
  metadata?: { expected?: Array<string | { path: string; relevance: number }> };
};

async function warmup(embeddingService: EmbeddingService): Promise<Map<string, string>> {
  return warmupClaims(TEST_CLAIMS, embeddingService);
}

async function warmupClaims(
  claims: Array<{
    id: string;
    text: string;
    kind: string;
    scope: string;
    boundary_class: string;
    content_hash: string;
    provenance: { at: string; actor: string; note: string };
  }>,
  embeddingService: EmbeddingService
): Promise<Map<string, string>> {
  const testIdToClaimId = new Map<string, string>();
  for (const claim of claims) {
    const result = await upsertClaimWithEmbedding(
      {
        text: claim.text,
        kind: claim.kind as ClaimKind,
        scope: claim.scope as 'session' | 'project' | 'principle',
        boundary_class: claim.boundary_class as 'public' | 'internal' | 'pii' | 'secret',
        content_hash: claim.content_hash,
        provenance: claim.provenance,
      },
      embeddingService
    );
    testIdToClaimId.set(claim.id, result.claim.id);
  }
  return testIdToClaimId;
}

function resolveExpectedId(
  rawId: string,
  testIdToClaimId: Map<string, string>,
  queryId: string
): string {
  const mapped = testIdToClaimId.get(rawId);
  if (!mapped) throw new Error(`Unknown expected claim "${rawId}" in query "${queryId}"`);
  return mapped;
}

async function runConfigQueries(
  config: AblationConfig,
  queries: QueryType[],
  testIdToClaimId: Map<string, string>,
  embeddingService: EmbeddingService
): Promise<AblationConfigResult> {
  const topK = 10;
  const perQuery: QueryMetrics[] = [];

  for (const query of queries) {
    const startTime = performance.now();
    const searchResult = await hybridSearchPaginated(
      ['session', 'project', 'principle'],
      topK,
      query.text,
      {
        embeddingService,
        alpha: config.alpha,
        kText: config.kText,
        kVec: config.kVec,
        enableRerank: config.enableRerank,
        mmr: config.mmr.enabled
          ? { enabled: true, lambda: config.mmr.lambda ?? 0.72, maxCandidates: 48 }
          : undefined,
        intent: config.intent,
      }
    );
    const latencyMs = performance.now() - startTime;
    const retrievedIds = searchResult.results.map((c) => c.claim.id);

    const relevanceGrades = new Map<string, number>();
    const relevantIdSet = new Set<string>();
    if (Array.isArray(query.metadata?.expected)) {
      for (const item of query.metadata!.expected!) {
        if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
          const cid = resolveExpectedId(item.path, testIdToClaimId, query.id);
          relevanceGrades.set(cid, item.relevance);
          if (item.relevance > 0) relevantIdSet.add(cid);
        } else if (typeof item === 'string') {
          const cid = resolveExpectedId(item, testIdToClaimId, query.id);
          relevanceGrades.set(cid, 1);
          relevantIdSet.add(cid);
        }
      }
    }

    const evalStartTime = Date.now();
    const metrics = evaluateRetrieval({
      items: retrievedIds.map((id, i) => ({
        id,
        timestampMs: evalStartTime + i * TIMESTAMP_INTERVAL_MS,
      })),
      relevant: Array.from(relevantIdSet),
      k: topK,
      startTimestampMs: evalStartTime,
      ...(relevanceGrades.size > 0 && { relevanceGrades }),
    });

    perQuery.push({
      queryId: query.id,
      precision: metrics.precisionAtK,
      recall: metrics.recallAtK,
      mrr: metrics.mrr,
      ndcg: metrics.ndcg ?? 0,
      latencyMs,
    });
  }

  const avg = (arr: number[]) => (arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0);
  return {
    config,
    avgPrecision: avg(perQuery.map((r) => r.precision)),
    avgRecall: avg(perQuery.map((r) => r.recall)),
    avgMrr: avg(perQuery.map((r) => r.mrr)),
    avgNdcg: avg(perQuery.map((r) => r.ndcg)),
    avgLatencyMs: avg(perQuery.map((r) => r.latencyMs)),
    perQuery,
  };
}

const RERANK_ABLATION_CLAIM_COUNT = 150;

const RERANK_CONFIGS: AblationConfig[] = [
  {
    name: 'hybrid-no-rerank',
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: false,
    mmr: { enabled: false },
  },
  {
    name: BASELINE_NAME,
    alpha: 0.65,
    kText: 128,
    kVec: 256,
    enableRerank: true,
    mmr: { enabled: false },
  },
];

async function runRerankAblation(
  embeddingService: EmbeddingService,
  queries: QueryType[]
): Promise<RerankAblationResult> {
  console.log(`  [ablation] Rerank ablation with ${RERANK_ABLATION_CLAIM_COUNT} claims...`);
  const claims = generateClaims(RERANK_ABLATION_CLAIM_COUNT);
  const results: AblationConfigResult[] = [];

  for (const config of RERANK_CONFIGS) {
    console.log(`  [ablation] Rerank ablation: ${config.name}`);
    await resetDbAsync();
    await initDb();
    await initSchema();
    setEmbeddingService(embeddingService);
    const idMap = await warmupClaims(claims, embeddingService);
    const result = await runConfigQueries(config, queries, idMap, embeddingService);
    results.push(result);
    console.log(
      `    P=${(result.avgPrecision * 100).toFixed(1)}% R=${(result.avgRecall * 100).toFixed(1)}% MRR=${(result.avgMrr * 100).toFixed(1)}% nDCG=${(result.avgNdcg * 100).toFixed(1)}%`
    );
  }

  const withoutRerank = results.find((r) => r.config.name === 'hybrid-no-rerank')!;
  const withRerank = results.find((r) => r.config.name === BASELINE_NAME)!;

  return {
    claimCount: RERANK_ABLATION_CLAIM_COUNT,
    withRerank,
    withoutRerank,
    delta: {
      configName: 'rerank-effect',
      deltaPrecision: withRerank.avgPrecision - withoutRerank.avgPrecision,
      deltaRecall: withRerank.avgRecall - withoutRerank.avgRecall,
      deltaMrr: withRerank.avgMrr - withoutRerank.avgMrr,
      deltaNdcg: withRerank.avgNdcg - withoutRerank.avgNdcg,
    },
  };
}

export async function runAblation(
  embeddingService: EmbeddingService,
  datasetPath: string
): Promise<AblationResult> {
  const dataset = await loadDataset(datasetPath);
  const queries = dataset.queries as QueryType[];
  const configs: AblationConfigResult[] = [];

  process.env.PCE_DB = ':memory:';
  for (const config of ABLATION_CONFIGS) {
    console.log(`  [ablation] Running: ${config.name}`);
    await resetDbAsync();
    await initDb();
    await initSchema();
    setEmbeddingService(embeddingService);
    const idMap = await warmup(embeddingService);
    const result = await runConfigQueries(config, queries, idMap, embeddingService);
    configs.push(result);
    console.log(
      `    P=${(result.avgPrecision * 100).toFixed(1)}% R=${(result.avgRecall * 100).toFixed(1)}% MRR=${(result.avgMrr * 100).toFixed(1)}% nDCG=${(result.avgNdcg * 100).toFixed(1)}%`
    );
  }

  const baseline = configs.find((c) => c.config.name === BASELINE_NAME);
  const deltas: AblationDelta[] = configs.map((c) => ({
    configName: c.config.name,
    deltaPrecision: baseline ? c.avgPrecision - baseline.avgPrecision : 0,
    deltaRecall: baseline ? c.avgRecall - baseline.avgRecall : 0,
    deltaMrr: baseline ? c.avgMrr - baseline.avgMrr : 0,
    deltaNdcg: baseline ? c.avgNdcg - baseline.avgNdcg : 0,
  }));

  // Large-corpus rerank ablation to detect g() effect
  const rerankAblation = await runRerankAblation(embeddingService, queries);

  return { configs, baselineName: BASELINE_NAME, deltas, rerankAblation };
}

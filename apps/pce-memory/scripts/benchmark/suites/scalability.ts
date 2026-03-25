/**
 * Scalability benchmark: measure quality/latency degradation as corpus grows.
 *
 * Data points: 15, 100, 500, 1000, 5000 claims.
 */

import { performance } from 'node:perf_hooks';
import { evaluateRetrieval } from '../../../external/assay-kit/packages/assay-kit/src/metrics/combined.ts';
import { loadDataset } from '../../../external/assay-kit/packages/assay-kit/src/dataset/loader.ts';
import { initDb, initSchema, resetDbAsync } from '../../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
import type { ClaimKind } from '../../../src/domain/types';
import { generateClaims, type SyntheticClaim } from '../data/synthetic-claims';
import { computeLatencyStats, type ScalabilityDataPoint, type ScalabilityResult } from '../types';

const SCALE_POINTS = [15, 100, 500, 1000, 5000];
const SEARCH_REPETITIONS = 3;
const TOP_K = 10;

type QueryType = {
  id: string;
  text: string;
  metadata?: { expected?: Array<string | { path: string; relevance: number }> };
};

async function warmupClaims(
  claims: SyntheticClaim[],
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

async function measureScalePoint(
  claimCount: number,
  queries: QueryType[],
  embeddingService: EmbeddingService
): Promise<ScalabilityDataPoint> {
  console.log(`  [scalability] Seeding ${claimCount} claims...`);
  process.env.PCE_DB = ':memory:';
  await resetDbAsync();
  await initDb();
  await initSchema();
  setEmbeddingService(embeddingService);

  const claims = generateClaims(claimCount);
  const idMap = await warmupClaims(claims, embeddingService);
  console.log(`  [scalability] Running ${queries.length} queries × ${SEARCH_REPETITIONS} reps...`);

  const allPrecisions: number[] = [];
  const allRecalls: number[] = [];
  const allPrecisionsAt5: number[] = [];
  const allRecallsAt5: number[] = [];
  const allMrrs: number[] = [];
  const allNdcgs: number[] = [];
  const allLatencies: number[] = [];

  for (let rep = 0; rep < SEARCH_REPETITIONS; rep++) {
    for (const query of queries) {
      const startTime = performance.now();
      const searchResult = await hybridSearchPaginated(
        ['session', 'project', 'principle'],
        TOP_K,
        query.text,
        { embeddingService, alpha: 0.65, enableRerank: true }
      );
      const latencyMs = performance.now() - startTime;
      allLatencies.push(latencyMs);

      // Only compute IR metrics on first rep (deterministic)
      if (rep === 0) {
        const retrievedIds = searchResult.results.map((c) => c.claim.id);
        const relevanceGrades = new Map<string, number>();
        const relevantIdSet = new Set<string>();

        if (Array.isArray(query.metadata?.expected)) {
          for (const item of query.metadata!.expected!) {
            if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
              const cid = resolveExpectedId(item.path, idMap, query.id);
              relevanceGrades.set(cid, item.relevance);
              if (item.relevance > 0) relevantIdSet.add(cid);
            } else if (typeof item === 'string') {
              const cid = resolveExpectedId(item, idMap, query.id);
              relevanceGrades.set(cid, 1);
              relevantIdSet.add(cid);
            }
          }
        }

        const evalStartTime = Date.now();
        const evalItems = retrievedIds.map((id, i) => ({
          id,
          timestampMs: evalStartTime + i * 10,
        }));
        const relevantArray = Array.from(relevantIdSet);
        const gradesOpt = relevanceGrades.size > 0 ? { relevanceGrades } : {};

        const metricsAt10 = evaluateRetrieval({
          items: evalItems,
          relevant: relevantArray,
          k: TOP_K,
          startTimestampMs: evalStartTime,
          ...gradesOpt,
        });

        const metricsAt5 = evaluateRetrieval({
          items: evalItems,
          relevant: relevantArray,
          k: 5,
          startTimestampMs: evalStartTime,
          ...gradesOpt,
        });

        allPrecisions.push(metricsAt10.precisionAtK);
        allRecalls.push(metricsAt10.recallAtK);
        allPrecisionsAt5.push(metricsAt5.precisionAtK);
        allRecallsAt5.push(metricsAt5.recallAtK);
        allMrrs.push(metricsAt10.mrr);
        allNdcgs.push(metricsAt10.ndcg ?? 0);
      }
    }
  }

  const avg = (arr: number[]) => (arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0);

  const result: ScalabilityDataPoint = {
    claimCount,
    avgPrecision: avg(allPrecisions),
    avgRecall: avg(allRecalls),
    avgPrecisionAt5: avg(allPrecisionsAt5),
    avgRecallAt5: avg(allRecallsAt5),
    avgMrr: avg(allMrrs),
    avgNdcg: avg(allNdcgs),
    latency: computeLatencyStats(allLatencies),
  };

  console.log(
    `    ${claimCount} claims: P=${(result.avgPrecision * 100).toFixed(1)}% R=${(result.avgRecall * 100).toFixed(1)}% MRR=${(result.avgMrr * 100).toFixed(1)}% p50=${result.latency.p50.toFixed(0)}ms`
  );

  return result;
}

export async function runScalability(
  embeddingService: EmbeddingService,
  datasetPath: string
): Promise<ScalabilityResult> {
  const dataset = await loadDataset(datasetPath);
  const queries = dataset.queries as QueryType[];
  const dataPoints: ScalabilityDataPoint[] = [];

  for (const count of SCALE_POINTS) {
    const dp = await measureScalePoint(count, queries, embeddingService);
    dataPoints.push(dp);
  }

  return { dataPoints };
}

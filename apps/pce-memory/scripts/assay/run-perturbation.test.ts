/**
 * Vitest wrapper for perturbation test.
 */
import { describe, it, expect } from 'vitest';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { loadDataset, evaluateRetrieval } from '../../external/assay-kit/packages/assay-kit/src/index.ts';
import { TEST_CLAIMS } from './test-data.ts';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
import {
  initLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';

const TIMESTAMP_INTERVAL_MS = 10;

interface PerturbationConfig {
  name: string;
  alpha: number;
  rerank: boolean;
  top_k: number;
}

const CONFIGS: PerturbationConfig[] = [
  { name: 'baseline', alpha: 0.65, rerank: true, top_k: 10 },
  { name: 'no-rerank', alpha: 0.65, rerank: false, top_k: 10 },
  { name: 'alpha-0.5', alpha: 0.50, rerank: true, top_k: 10 },
  { name: 'alpha-0.8', alpha: 0.80, rerank: true, top_k: 10 },
  { name: 'top_k-5', alpha: 0.65, rerank: true, top_k: 5 },
  { name: 'top_k-20', alpha: 0.65, rerank: true, top_k: 20 },
];

let embeddingService: EmbeddingService;

async function initEmbeddings(): Promise<void> {
  await initLocalProvider();
  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  embeddingService = createLocalOnlyService(localProvider, cache);
  setEmbeddingService(embeddingService);
}

async function warmup(): Promise<Map<string, string>> {
  const testIdToClaimId = new Map<string, string>();
  for (const claim of TEST_CLAIMS) {
    const result = await upsertClaimWithEmbedding(
      {
        text: claim.text,
        kind: claim.kind as 'fact' | 'preference' | 'task' | 'policy_hint',
        scope: claim.scope as 'session' | 'project' | 'principle',
        boundary_class: claim.boundary_class as 'public' | 'internal' | 'pii' | 'secret',
        content_hash: claim.content_hash,
        provenance: claim.provenance,
      },
      embeddingService,
    );
    testIdToClaimId.set(claim.id, result.claim.id);
  }
  return testIdToClaimId;
}

type QueryType = { id: string; text: string; metadata?: { expected?: Array<string | { path: string; relevance: number }> } };

interface ConfigResult {
  config: PerturbationConfig;
  avgPrecision: number;
  avgRecall: number;
  avgMrr: number;
  avgNdcg: number;
  results: Array<{ queryId: string; precision: number; recall: number; mrr: number; ndcg: number }>;
}

async function runConfig(
  config: PerturbationConfig,
  queries: QueryType[],
  testIdToClaimId: Map<string, string>,
): Promise<ConfigResult> {
  const results: ConfigResult['results'] = [];
  for (const query of queries) {
    const startTime = Date.now();
    const searchResult = await hybridSearchPaginated(
      ['session', 'project', 'principle'], config.top_k, query.text,
      { embeddingService, alpha: config.alpha, enableRerank: config.rerank },
    );
    const retrievedIds = searchResult.results.map((c) => c.claim.id);
    const relevanceGrades = new Map<string, number>();
    const relevantIds: string[] = [];
    if (Array.isArray(query.metadata?.expected)) {
      for (const item of query.metadata!.expected!) {
        if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
          const cid = testIdToClaimId.get(item.path) ?? item.path;
          relevanceGrades.set(cid, item.relevance);
          if (item.relevance > 0) relevantIds.push(cid);
        } else if (typeof item === 'string') {
          const cid = testIdToClaimId.get(item) ?? item;
          relevanceGrades.set(cid, 1);
          relevantIds.push(cid);
        }
      }
    }
    const metrics = evaluateRetrieval({
      items: retrievedIds.map((id, i) => ({ id, timestampMs: startTime + i * TIMESTAMP_INTERVAL_MS })),
      relevant: relevantIds, k: config.top_k, startTimestampMs: startTime,
      ...(relevanceGrades.size > 0 && { relevanceGrades }),
    });
    results.push({ queryId: query.id, precision: metrics.precisionAtK, recall: metrics.recallAtK, mrr: metrics.mrr, ndcg: metrics.ndcg ?? 0 });
  }
  const avg = (arr: number[]) => arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0;
  return { config, results, avgPrecision: avg(results.map(r => r.precision)), avgRecall: avg(results.map(r => r.recall)), avgMrr: avg(results.map(r => r.mrr)), avgNdcg: avg(results.map(r => r.ndcg)) };
}

describe('PCE-Memory Parameter Perturbation', () => {
  it('compares search quality across configs', async () => {
    const repoRoot = join(import.meta.dirname, '../..');
    const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
    const resultsDir = join(repoRoot, 'var/assay');
    if (!existsSync(resultsDir)) mkdirSync(resultsDir, { recursive: true });

    await initEmbeddings();
    const dataset = await loadDataset(datasetPath);
    const queries = dataset.queries as QueryType[];
    console.log(`Loaded ${queries.length} queries`);

    const configResults: ConfigResult[] = [];
    for (const config of CONFIGS) {
      console.log(`Running: ${config.name}`);
      await resetDbAsync();
      process.env.PCE_DB = ':memory:';
      await initDb();
      await initSchema();
      const idMap = await warmup();
      const result = await runConfig(config, queries, idMap);
      configResults.push(result);
      console.log(`  P=${(result.avgPrecision*100).toFixed(1)}% R=${(result.avgRecall*100).toFixed(1)}% MRR=${(result.avgMrr*100).toFixed(1)}% nDCG=${(result.avgNdcg*100).toFixed(1)}%`);
    }

    // Markdown output
    const lines = ['# Perturbation Results', '', `| Config | α | Rerank | top_k | Precision | Recall | MRR | nDCG |`, `|--------|---|--------|-------|-----------|--------|-----|------|`];
    for (const cr of configResults) {
      lines.push(`| ${cr.config.name} | ${cr.config.alpha} | ${cr.config.rerank ? 'on' : 'off'} | ${cr.config.top_k} | ${(cr.avgPrecision*100).toFixed(1)}% | ${(cr.avgRecall*100).toFixed(1)}% | ${(cr.avgMrr*100).toFixed(1)}% | ${(cr.avgNdcg*100).toFixed(1)}% |`);
    }
    const dateStr = new Date().toISOString().split('T')[0];
    const mdPath = join(resultsDir, `perturbation-${dateStr}.md`);
    writeFileSync(mdPath, lines.join('\n'));
    console.log(`\nResults: ${mdPath}`);

    // Quality gates
    expect(configResults).toHaveLength(CONFIGS.length);
    for (const cr of configResults) {
      expect(cr.results).toHaveLength(queries.length);
      expect(Number.isFinite(cr.avgRecall)).toBe(true);
      expect(Number.isFinite(cr.avgMrr)).toBe(true);
    }
    const baseline = configResults.find((c) => c.config.name === 'baseline');
    expect(baseline).toBeDefined();
    expect(baseline!.avgRecall).toBeGreaterThan(0.5);
  });
});

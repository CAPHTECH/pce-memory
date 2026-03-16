/**
 * Vitest wrapper for goldenset evaluation.
 * vitestのモジュール解決（resolve.alias）を活用してfp-ts等のESM問題を回避。
 */
import { describe, it, expect } from 'vitest';
import { existsSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';

import {
  loadDataset,
  Runner,
  JsonReporter,
  MarkdownReporter,
  ConsoleReporter,
  evaluateRetrieval,
} from '../../external/assay-kit/packages/assay-kit/src/index.ts';

import type {
  SearchAdapter,
  SearchAdapterContext,
  Metrics,
  Query,
  Dataset,
} from '../../external/assay-kit/packages/assay-kit/src/index.ts';

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

interface PceQueryMetadata extends Record<string, unknown> {
  category?: string;
  intent?: string;
  expected?: Array<string | { path: string; relevance: number }>;
}

type PceQuery = Query<Record<string, unknown>, PceQueryMetadata>;

class StoreDirectAdapter implements SearchAdapter<PceQuery, Metrics> {
  private testIdToClaimId = new Map<string, string>();
  private embeddingService!: EmbeddingService;

  async warmup(_dataset: Dataset<PceQuery>): Promise<void> {
    await initLocalProvider();
    const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
    this.embeddingService = createLocalOnlyService(localProvider, cache);
    setEmbeddingService(this.embeddingService);

    await resetDbAsync();
    process.env.PCE_DB = ':memory:';
    await initDb();
    await initSchema();

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
        this.embeddingService,
      );
      this.testIdToClaimId.set(claim.id, result.claim.id);
    }
  }

  async execute(query: PceQuery, ctx: SearchAdapterContext): Promise<Metrics> {
    const startTime = Date.now();
    if (ctx.signal.aborted) throw new Error(`Query ${query.id} was cancelled`);
    const k = ctx.options.k ?? 10;

    const searchResult = await hybridSearchPaginated(
      ['session', 'project', 'principle'],
      k,
      query.text,
      { embeddingService: this.embeddingService },
    );

    const latencyMs = Date.now() - startTime;
    const retrievedIds = searchResult.results.map((c) => c.claim.id);
    const { relevanceGrades, relevantIds } = this.buildRelevanceGrades(query);

    const retrievalMetrics = evaluateRetrieval({
      items: retrievedIds.map((id, i) => ({
        id,
        timestampMs: startTime + i * TIMESTAMP_INTERVAL_MS,
      })),
      relevant: relevanceGrades.size > 0 ? relevantIds : this.getExpectedIds(query),
      k,
      startTimestampMs: startTime,
      ...(relevanceGrades.size > 0 && { relevanceGrades }),
    });

    return {
      latencyMs,
      precision: retrievalMetrics.precisionAtK,
      recall: retrievalMetrics.recallAtK,
      extras: {
        resultCount: retrievedIds.length,
        k,
        mrr: retrievalMetrics.mrr,
        map: retrievalMetrics.map,
        hitsAtK: retrievalMetrics.hitsAtK,
        f1: retrievalMetrics.f1,
        ttfu: retrievalMetrics.timeToFirstUseful,
        ndcg: retrievalMetrics.ndcg ?? 0,
      },
    };
  }

  async stop(): Promise<void> {}

  private getExpectedIds(query: PceQuery): string[] {
    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) return [];
    return expected.map((item) => {
      const testId = typeof item === 'string' ? item : item.path;
      return this.resolveExpectedId(testId);
    });
  }

  private resolveExpectedId(rawId: string): string {
    const mapped = this.testIdToClaimId.get(rawId);
    if (!mapped) throw new Error(`Unknown expected claim reference "${rawId}"`);
    return mapped;
  }

  private buildRelevanceGrades(query: PceQuery): {
    relevanceGrades: Map<string, number>;
    relevantIds: string[];
  } {
    const relevanceGrades = new Map<string, number>();
    const relevantIdSet = new Set<string>();
    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) return { relevanceGrades, relevantIds: [] };
    for (const item of expected) {
      if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
        const claimId = this.resolveExpectedId(item.path);
        relevanceGrades.set(claimId, item.relevance);
        if (item.relevance > 0) relevantIdSet.add(claimId);
      } else if (typeof item === 'string') {
        const claimId = this.resolveExpectedId(item);
        relevanceGrades.set(claimId, 1);
        relevantIdSet.add(claimId);
      }
    }
    return { relevanceGrades, relevantIds: Array.from(relevantIdSet) };
  }
}

describe('PCE-Memory Goldenset Evaluation', () => {
  it('evaluates search quality with embeddings', async () => {
    const repoRoot = join(import.meta.dirname, '../..');
    const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
    const resultsDir = join(repoRoot, 'var/assay');

    if (!existsSync(resultsDir)) mkdirSync(resultsDir, { recursive: true });

    const dataset = await loadDataset(datasetPath);
    console.log(`Loaded ${dataset.queries.length} queries from ${dataset.name}`);

    const adapter = new StoreDirectAdapter();
    const runner = new Runner({ adapter, warmupRuns: 1, concurrency: 1, maxRetries: 2 });
    const result = await runner.evaluate(dataset);

    const dateStr = new Date().toISOString().split('T')[0];
    const baseName = `eval-${dataset.name.replace(/[^a-zA-Z0-9_-]+/g, '-')}-${dateStr}`;
    const jsonPath = join(resultsDir, `${baseName}.json`);
    const mdPath = join(resultsDir, `${baseName}.md`);

    await new JsonReporter({ outputPath: jsonPath }).write(result);
    await new MarkdownReporter({ outputPath: mdPath }).write(result);
    await new ConsoleReporter({ verbosity: 'normal' }).write(result);

    const avg = (arr: number[]) => arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0;
    const precisions = result.queries.filter((q) => q.status === 'success').map((q) => q.metrics?.precision ?? 0);
    const recalls = result.queries.filter((q) => q.status === 'success').map((q) => q.metrics?.recall ?? 0);
    const mrrs = result.queries.filter((q) => q.status === 'success').map((q) => (q.metrics?.extras?.mrr as number) ?? 0);
    const ndcgs = result.queries.filter((q) => q.status === 'success').map((q) => (q.metrics?.extras?.ndcg as number) ?? 0);

    console.log(`\n📊 Metrics Summary:`);
    console.log(`  Precision@k: ${(avg(precisions) * 100).toFixed(1)}%`);
    console.log(`  Recall@k: ${(avg(recalls) * 100).toFixed(1)}%`);
    console.log(`  MRR: ${(avg(mrrs) * 100).toFixed(1)}%`);
    console.log(`  nDCG: ${(avg(ndcgs) * 100).toFixed(1)}%`);
    console.log(`\n📄 Results: ${jsonPath}\n  ${mdPath}`);

    // Quality gates
    expect(result.overall.errorCount).toBe(0);
    expect(result.overall.successCount).toBe(dataset.queries.length);
    expect(avg(recalls)).toBeGreaterThan(0.5);
    expect(avg(mrrs)).toBeGreaterThan(0.5);
  });
});

#!/usr/bin/env tsx
/**
 * PCE-Memory Goldenset Evaluation Runner (Store直接方式)
 *
 * store層を直接使い、embedding有効状態でactivate検索精度を評価する。
 * assay-kitのRunner/Reporterを使用してメトリクスを集計・出力。
 *
 * Usage:
 *   pnpm assay:evaluate
 *   pnpm assay:evaluate --dataset path/to/custom.yaml
 */

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

// store層の直接インポート
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection.ts';
import { upsertClaimWithEmbedding } from '../../src/store/claims.ts';
import { hybridSearchPaginated, setEmbeddingService } from '../../src/store/hybridSearch.ts';
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

/**
 * Store直接方式のSearchAdapter
 */
class StoreDirectAdapter implements SearchAdapter<PceQuery, Metrics> {
  private testIdToClaimId = new Map<string, string>();
  private embeddingService!: EmbeddingService;

  async warmup(_dataset: Dataset<PceQuery>): Promise<void> {
    // EmbeddingService初期化
    console.log('🧠 Initializing embedding service...');
    await initLocalProvider();
    const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
    this.embeddingService = createLocalOnlyService(localProvider, cache);
    setEmbeddingService(this.embeddingService);
    console.log('  Embedding service ready');

    // DB初期化
    await resetDbAsync();
    process.env.PCE_DB = ':memory:';
    await initDb();
    await initSchema();

    // テストデータ投入（embedding付き）
    console.log(`📝 Upserting ${TEST_CLAIMS.length} test claims with embeddings...`);
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
        this.embeddingService
      );
      this.testIdToClaimId.set(claim.id, result.claim.id);
    }
    console.log('✅ Warmup completed');
  }

  async execute(query: PceQuery, ctx: SearchAdapterContext): Promise<Metrics> {
    const startTime = Date.now();

    if (ctx.signal.aborted) {
      throw new Error(`Query ${query.id} was cancelled`);
    }

    const k = ctx.options.k ?? 10;

    const searchResult = await hybridSearchPaginated(
      ['session', 'project', 'principle'],
      k,
      query.text,
      {
        embeddingService: this.embeddingService,
      }
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

  async stop(_reason?: string): Promise<void> {
    // store直接方式ではdaemon停止不要
  }

  private getExpectedIds(query: PceQuery): string[] {
    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) return [];
    return expected
      .map((item) => {
        const testId = typeof item === 'string' ? item : item.path;
        return this.testIdToClaimId.get(testId) ?? testId;
      })
      .filter(Boolean);
  }

  private buildRelevanceGrades(query: PceQuery): {
    relevanceGrades: Map<string, number>;
    relevantIds: string[];
  } {
    const relevanceGrades = new Map<string, number>();
    const relevantIds: string[] = [];
    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) return { relevanceGrades, relevantIds };

    for (const item of expected) {
      if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
        const claimId = this.testIdToClaimId.get(item.path) ?? item.path;
        relevanceGrades.set(claimId, item.relevance);
        if (item.relevance > 0) relevantIds.push(claimId);
      } else if (typeof item === 'string') {
        const claimId = this.testIdToClaimId.get(item) ?? item;
        relevanceGrades.set(claimId, 1);
        relevantIds.push(claimId);
      }
    }
    return { relevanceGrades, relevantIds };
  }
}

function parseDatasetArg(defaultPath: string): string {
  const args = process.argv.slice(2);
  const index = args.indexOf('--dataset');
  if (index === -1) return defaultPath;
  const value = args[index + 1];
  if (!value) throw new Error('Missing value for --dataset.');
  return value;
}

async function main(): Promise<void> {
  console.log('🎯 PCE-Memory Goldenset Evaluation (Store Direct)\n');

  const repoRoot = join(import.meta.dirname, '../..');
  const defaultDatasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const datasetPath = parseDatasetArg(defaultDatasetPath);
  const resultsDir = join(repoRoot, 'var/assay');

  if (!existsSync(datasetPath)) {
    throw new Error(`Dataset not found at ${datasetPath}.`);
  }
  if (!existsSync(resultsDir)) {
    mkdirSync(resultsDir, { recursive: true });
  }

  console.log('📖 Loading dataset...');
  const dataset = await loadDataset(datasetPath);
  console.log(`  Loaded ${dataset.queries.length} queries from ${dataset.name}`);

  const adapter = new StoreDirectAdapter();

  const runner = new Runner({
    adapter,
    warmupRuns: 1,
    concurrency: 1,
    maxRetries: 2,
  });

  console.log('🚀 Running evaluation...\n');
  const result = await runner.evaluate(dataset);

  // 結果出力
  const dateStr = new Date().toISOString().split('T')[0];
  const datasetSlug = dataset.name.replace(/[^a-zA-Z0-9_-]+/g, '-');
  const baseName = `eval-${datasetSlug}-${dateStr}`;
  const jsonPath = join(resultsDir, `${baseName}.json`);
  const mdPath = join(resultsDir, `${baseName}.md`);

  const jsonReporter = new JsonReporter({ outputPath: jsonPath });
  await jsonReporter.write(result);

  const mdReporter = new MarkdownReporter({ outputPath: mdPath });
  await mdReporter.write(result);

  const consoleReporter = new ConsoleReporter({ verbosity: 'normal' });
  await consoleReporter.write(result);

  console.log(`\n📄 Results written to:\n  JSON: ${jsonPath}\n  Markdown: ${mdPath}\n`);

  console.log('📊 Summary:');
  console.log(`  Total queries: ${result.dataset.totalQueries}`);
  console.log(`  Success: ${result.overall.successCount}`);
  console.log(`  Errors: ${result.overall.errorCount}`);
  console.log(`  Average latency: ${result.overall.avgLatencyMs.toFixed(1)}ms`);

  const precisions = result.queries
    .filter((q) => q.status === 'success' && q.metrics?.precision !== undefined)
    .map((q) => q.metrics!.precision!);
  const recalls = result.queries
    .filter((q) => q.status === 'success' && q.metrics?.recall !== undefined)
    .map((q) => q.metrics!.recall!);
  const mrrs = result.queries
    .filter((q) => q.status === 'success' && q.metrics?.extras?.mrr !== undefined)
    .map((q) => q.metrics!.extras!.mrr as number);
  const ndcgs = result.queries
    .filter((q) => q.status === 'success' && q.metrics?.extras?.ndcg !== undefined)
    .map((q) => q.metrics!.extras!.ndcg as number);

  const avg = (arr: number[]) => (arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0);
  console.log(`  Precision@k: ${(avg(precisions) * 100).toFixed(1)}%`);
  console.log(`  Recall@k: ${(avg(recalls) * 100).toFixed(1)}%`);
  console.log(`  MRR: ${(avg(mrrs) * 100).toFixed(1)}%`);
  console.log(`  nDCG: ${(avg(ndcgs) * 100).toFixed(1)}%`);

  process.exit(0);
}

main().catch((error) => {
  console.error(
    `\n❌ Evaluation failed: ${error instanceof Error ? error.message : String(error)}`
  );
  process.exit(1);
});

#!/usr/bin/env tsx
/**
 * PCE-Memory パラメータ摂動テストランナー
 *
 * store層を直接使い、パラメータを変えて検索品質を比較する。
 *
 * Usage:
 *   pnpm assay:perturbation
 */

import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import {
  loadDataset,
  evaluateRetrieval,
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

interface PerturbationConfig {
  name: string;
  alpha: number;
  rerank: boolean;
  top_k: number;
}

const CONFIGS: PerturbationConfig[] = [
  { name: 'baseline', alpha: 0.65, rerank: true, top_k: 10 },
  { name: 'no-rerank', alpha: 0.65, rerank: false, top_k: 10 },
  { name: 'alpha-0.5', alpha: 0.5, rerank: true, top_k: 10 },
  { name: 'alpha-0.8', alpha: 0.8, rerank: true, top_k: 10 },
  { name: 'top_k-5', alpha: 0.65, rerank: true, top_k: 5 },
  { name: 'top_k-20', alpha: 0.65, rerank: true, top_k: 20 },
];

interface QueryResult {
  queryId: string;
  retrievedIds: string[];
  precision: number;
  recall: number;
  mrr: number;
  ndcg: number;
}

interface ConfigResult {
  config: PerturbationConfig;
  results: QueryResult[];
  avgPrecision: number;
  avgRecall: number;
  avgMrr: number;
  avgNdcg: number;
}

const TIMESTAMP_INTERVAL_MS = 10;

let embeddingService: EmbeddingService;

/**
 * EmbeddingService初期化
 */
async function initEmbeddings(): Promise<void> {
  await initLocalProvider();
  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  embeddingService = createLocalOnlyService(localProvider, cache);
  setEmbeddingService(embeddingService);
}

/**
 * テストデータをDB投入する（埋め込みベクトル付き）
 */
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
      embeddingService
    );
    testIdToClaimId.set(claim.id, result.claim.id);
  }

  return testIdToClaimId;
}

/**
 * 単一設定でクエリ群を実行
 */
async function runConfig(
  config: PerturbationConfig,
  queries: Array<{
    id: string;
    text: string;
    metadata?: { expected?: Array<string | { path: string; relevance: number }> };
  }>,
  testIdToClaimId: Map<string, string>
): Promise<ConfigResult> {
  const results: QueryResult[] = [];

  for (const query of queries) {
    const startTime = Date.now();

    // hybridSearchPaginatedを直接呼び出し
    const searchResult = await hybridSearchPaginated(
      ['session', 'project', 'principle'],
      config.top_k,
      query.text,
      {
        embeddingService,
        alpha: config.alpha,
        enableRerank: config.rerank,
      }
    );

    const retrievedIds = searchResult.results.map((c) => c.claim.id);

    // expectedからrelevant IDsを構築
    const expected = query.metadata?.expected;
    const relevanceGrades = new Map<string, number>();
    const relevantIdSet = new Set<string>();
    const resolveId = (rawId: string): string => {
      const mapped = testIdToClaimId.get(rawId);
      if (!mapped)
        throw new Error(`Unknown expected claim reference "${rawId}" in query "${query.id}"`);
      return mapped;
    };

    if (Array.isArray(expected)) {
      for (const item of expected) {
        if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
          const claimId = resolveId(item.path);
          relevanceGrades.set(claimId, item.relevance);
          if (item.relevance > 0) {
            relevantIdSet.add(claimId);
          }
        } else if (typeof item === 'string') {
          const claimId = resolveId(item);
          relevanceGrades.set(claimId, 1);
          relevantIdSet.add(claimId);
        }
      }
    }

    const metrics = evaluateRetrieval({
      items: retrievedIds.map((id: string, i: number) => ({
        id,
        timestampMs: startTime + i * TIMESTAMP_INTERVAL_MS,
      })),
      relevant: Array.from(relevantIdSet),
      k: config.top_k,
      startTimestampMs: startTime,
      ...(relevanceGrades.size > 0 && { relevanceGrades }),
    });

    results.push({
      queryId: query.id,
      retrievedIds,
      precision: metrics.precisionAtK,
      recall: metrics.recallAtK,
      mrr: metrics.mrr,
      ndcg: metrics.ndcg ?? 0,
    });
  }

  const avg = (arr: number[]) => (arr.length > 0 ? arr.reduce((a, b) => a + b, 0) / arr.length : 0);

  return {
    config,
    results,
    avgPrecision: avg(results.map((r) => r.precision)),
    avgRecall: avg(results.map((r) => r.recall)),
    avgMrr: avg(results.map((r) => r.mrr)),
    avgNdcg: avg(results.map((r) => r.ndcg)),
  };
}

/**
 * Markdown比較テーブルを生成
 */
function generateMarkdown(configResults: ConfigResult[]): string {
  const lines: string[] = [];
  const dateStr = new Date().toISOString();

  lines.push(`# PCE-Memory パラメータ摂動テスト結果`);
  lines.push(``);
  lines.push(`Generated: ${dateStr}`);
  lines.push(``);
  lines.push(`## Summary`);
  lines.push(``);
  lines.push(`| Config | α | Rerank | top_k | Precision | Recall | MRR | nDCG |`);
  lines.push(`|--------|-----|--------|-------|-----------|--------|-----|------|`);

  for (const cr of configResults) {
    lines.push(
      `| ${cr.config.name} | ${cr.config.alpha} | ${cr.config.rerank ? 'on' : 'off'} | ${cr.config.top_k} | ${(cr.avgPrecision * 100).toFixed(1)}% | ${(cr.avgRecall * 100).toFixed(1)}% | ${(cr.avgMrr * 100).toFixed(1)}% | ${(cr.avgNdcg * 100).toFixed(1)}% |`
    );
  }

  lines.push(``);
  lines.push(`## Delta from Baseline`);
  lines.push(``);

  const baseline = configResults[0];
  lines.push(`| Config | ΔPrecision | ΔRecall | ΔMRR | ΔnDCG |`);
  lines.push(`|--------|------------|---------|------|-------|`);

  for (const cr of configResults) {
    const dp = ((cr.avgPrecision - baseline.avgPrecision) * 100).toFixed(1);
    const dr = ((cr.avgRecall - baseline.avgRecall) * 100).toFixed(1);
    const dm = ((cr.avgMrr - baseline.avgMrr) * 100).toFixed(1);
    const dn = ((cr.avgNdcg - baseline.avgNdcg) * 100).toFixed(1);
    const sign = (v: string) => (parseFloat(v) >= 0 ? `+${v}` : v);
    lines.push(
      `| ${cr.config.name} | ${sign(dp)}pp | ${sign(dr)}pp | ${sign(dm)}pp | ${sign(dn)}pp |`
    );
  }

  lines.push(``);
  lines.push(`## Per-Query Details`);
  lines.push(``);

  for (const cr of configResults) {
    lines.push(
      `### ${cr.config.name} (α=${cr.config.alpha}, rerank=${cr.config.rerank}, top_k=${cr.config.top_k})`
    );
    lines.push(``);
    lines.push(`| Query | Precision | Recall | MRR | nDCG |`);
    lines.push(`|-------|-----------|--------|-----|------|`);
    for (const r of cr.results) {
      lines.push(
        `| ${r.queryId} | ${(r.precision * 100).toFixed(1)}% | ${(r.recall * 100).toFixed(1)}% | ${(r.mrr * 100).toFixed(1)}% | ${(r.ndcg * 100).toFixed(1)}% |`
      );
    }
    lines.push(``);
  }

  return lines.join('\n');
}

async function main(): Promise<void> {
  console.log('🔬 PCE-Memory Parameter Perturbation Test\n');

  const repoRoot = join(import.meta.dirname, '../..');
  const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const resultsDir = join(repoRoot, 'var/assay');

  if (!existsSync(datasetPath)) {
    throw new Error(`Dataset not found at ${datasetPath}`);
  }
  if (!existsSync(resultsDir)) {
    mkdirSync(resultsDir, { recursive: true });
  }

  // EmbeddingService初期化
  console.log('🧠 Initializing embedding service...');
  await initEmbeddings();
  console.log('  Embedding service ready');

  // データセットロード
  console.log('📖 Loading dataset...');
  const dataset = await loadDataset(datasetPath);
  const queries = dataset.queries as Array<{
    id: string;
    text: string;
    metadata?: { expected?: Array<string | { path: string; relevance: number }> };
  }>;
  console.log(`  Loaded ${queries.length} queries`);

  const configResults: ConfigResult[] = [];
  process.env.PCE_DB = ':memory:';

  for (const config of CONFIGS) {
    console.log(
      `\n🔧 Running config: ${config.name} (α=${config.alpha}, rerank=${config.rerank}, top_k=${config.top_k})`
    );

    // 各設定ごとにDB初期化
    await resetDbAsync();
    await initDb();
    await initSchema();

    // テストデータ投入
    const testIdToClaimId = await warmup();
    console.log(`  Loaded ${TEST_CLAIMS.length} claims`);

    // クエリ実行
    const result = await runConfig(config, queries, testIdToClaimId);
    configResults.push(result);
    console.log(
      `  Precision: ${(result.avgPrecision * 100).toFixed(1)}%, Recall: ${(result.avgRecall * 100).toFixed(1)}%, MRR: ${(result.avgMrr * 100).toFixed(1)}%, nDCG: ${(result.avgNdcg * 100).toFixed(1)}%`
    );
  }

  // Markdown出力
  const dateStr = new Date().toISOString().split('T')[0];
  const mdPath = join(resultsDir, `perturbation-${dateStr}.md`);
  const markdown = generateMarkdown(configResults);
  writeFileSync(mdPath, markdown);

  console.log(`\n📄 Results written to: ${mdPath}`);
  console.log('\n✅ Perturbation test complete');

  process.exit(0);
}

main().catch((error) => {
  console.error(
    `\n❌ Perturbation test failed: ${error instanceof Error ? error.message : String(error)}`
  );
  process.exit(1);
});

#!/usr/bin/env tsx
/**
 * PCE-Memory Goldenset Evaluation Runner
 *
 * assay-kitを使用してpce-memoryのactivate検索精度を評価する。
 *
 * Usage:
 *   pnpm assay:evaluate
 *   pnpm assay:evaluate --dataset path/to/custom.yaml
 */

import { existsSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import * as os from 'node:os';

import {
  loadDataset,
  Runner,
  JsonReporter,
  MarkdownReporter,
  ConsoleReporter,
} from '../../external/assay-kit/packages/assay-kit/src/index.ts';

import { createPceMemoryAdapter } from './pce-adapter.ts';

/**
 * CLI引数からデータセットパスを取得
 */
function parseDatasetArg(defaultPath: string): string {
  const args = process.argv.slice(2);
  const index = args.indexOf('--dataset');
  if (index === -1) {
    return defaultPath;
  }
  const value = args[index + 1];
  if (!value) {
    throw new Error('Missing value for --dataset. Pass a path to a dataset YAML.');
  }
  return value;
}

/**
 * メイン関数
 */
async function main(): Promise<void> {
  console.log('🎯 PCE-Memory Goldenset Evaluation\n');

  const repoRoot = join(import.meta.dirname, '../..');
  const defaultDatasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const datasetPath = parseDatasetArg(defaultDatasetPath);
  const resultsDir = join(repoRoot, 'var/assay');

  // 一時DBパスを生成（評価ごとに新規作成）
  const tmpDir = os.tmpdir();
  const timestamp = Date.now();
  const databasePath = join(tmpDir, `pce-memory-eval-${timestamp}.duckdb`);

  if (!existsSync(datasetPath)) {
    throw new Error(`Dataset not found at ${datasetPath}.`);
  }
  if (!existsSync(resultsDir)) {
    mkdirSync(resultsDir, { recursive: true });
  }

  console.log('📖 Loading dataset...');
  const dataset = await loadDataset(datasetPath);
  console.log(`  Loaded ${dataset.queries.length} queries from ${dataset.name}`);

  const adapter = createPceMemoryAdapter(databasePath, repoRoot);

  const runner = new Runner({
    adapter,
    warmupRuns: 1,
    concurrency: 1, // pce-memoryはシーケンシャル実行
    maxRetries: 2,
  });

  console.log('🚀 Running evaluation...\n');

  let result: Awaited<ReturnType<Runner['evaluate']>>;
  try {
    result = await runner.evaluate(dataset);
  } finally {
    // 評価終了後にadapterを停止（daemonプロセス終了）
    await adapter.stop('evaluation-complete');
  }

  // 結果をファイル出力
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

  // サマリー表示（assay-kitのresult構造に合わせる）
  console.log('📊 Summary:');
  console.log(`  Total queries: ${result.dataset.totalQueries}`);
  console.log(`  Success: ${result.overall.successCount}`);
  console.log(`  Errors: ${result.overall.errorCount}`);
  console.log(`  Average latency: ${result.overall.avgLatencyMs.toFixed(1)}ms`);
  console.log(`  Total duration: ${result.overall.totalDurationMs}ms`);

  // 精度メトリクスの集計
  const precisions = result.queries
    .filter((q) => q.status === 'success' && q.metrics?.precision !== undefined)
    .map((q) => q.metrics!.precision!);

  if (precisions.length > 0) {
    const avgPrecision = precisions.reduce((a, b) => a + b, 0) / precisions.length;
    console.log(`  Average precision: ${(avgPrecision * 100).toFixed(1)}%`);
  }

  process.exit(0);
}

main().catch((error) => {
  console.error(
    `\n❌ Evaluation failed: ${error instanceof Error ? error.message : String(error)}`
  );
  process.exit(1);
});

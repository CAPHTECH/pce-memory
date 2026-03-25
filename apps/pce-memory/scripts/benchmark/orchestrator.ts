/**
 * Benchmark orchestrator: runs all suites and assembles the report.
 */

import { join } from 'node:path';
import { readFileSync } from 'node:fs';
import type { BenchmarkReport } from './types';
import { runAblation } from './suites/ablation';
import { runScalability } from './suites/scalability';
import { runLatencyProfile } from './suites/latency-profile';

export async function runBenchmark(): Promise<BenchmarkReport> {
  const repoRoot = join(import.meta.dirname, '../..');
  const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const pkgJson = JSON.parse(readFileSync(join(repoRoot, 'package.json'), 'utf-8'));

  // 1. Latency Profile first (before any other init, to measure true cold start)
  console.log('[benchmark] === Latency Profile ===');
  const { result: latencyProfile, embeddingService } = await runLatencyProfile();

  // 2. Ablation Study (reuses the already-initialized embedding service)
  console.log('\n[benchmark] === Ablation Study ===');
  const ablation = await runAblation(embeddingService, datasetPath);

  // 3. Scalability
  console.log('\n[benchmark] === Scalability ===');
  const scalability = await runScalability(embeddingService, datasetPath);

  const report: BenchmarkReport = {
    timestamp: new Date().toISOString(),
    version: pkgJson.version ?? 'unknown',
    environment: {
      node: process.version,
      platform: `${process.platform}/${process.arch}`,
      embeddingModel: 'all-MiniLM-L6-v2',
      embeddingDim: 384,
    },
    suites: {
      ablation,
      scalability,
      latencyProfile,
    },
  };

  console.log('\n[benchmark] Done.');
  return report;
}

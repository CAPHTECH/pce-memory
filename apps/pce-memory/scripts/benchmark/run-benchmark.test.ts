/**
 * Vitest entry point for pce-memory benchmark evaluation.
 *
 * Run: pnpm benchmark
 */

import { describe, it, expect } from 'vitest';
import { existsSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runBenchmark } from './orchestrator';
import { generateMarkdownReport } from './report/markdown-report';

const repoRoot = join(import.meta.dirname, '../..');
const assayKitEntry = join(
  repoRoot,
  'external/assay-kit/packages/assay-kit/src/metrics/combined.ts'
);
const benchmarkIt = existsSync(assayKitEntry) ? it : it.skip;

describe('PCE-Memory Benchmark', () => {
  benchmarkIt('generates comprehensive benchmark report', async () => {
    const resultsDir = join(repoRoot, 'var/benchmark');
    if (!existsSync(resultsDir)) mkdirSync(resultsDir, { recursive: true });

    const report = await runBenchmark();

    // Generate Markdown report
    const md = generateMarkdownReport(report);
    const dateStr = new Date().toISOString().split('T')[0];
    const mdPath = join(resultsDir, `benchmark-${dateStr}.md`);
    writeFileSync(mdPath, md);

    // Also write raw JSON for programmatic consumption
    const jsonPath = join(resultsDir, `benchmark-${dateStr}.json`);
    writeFileSync(jsonPath, JSON.stringify(report, null, 2));

    console.log(`\nReport: ${mdPath}`);
    console.log(`Data:   ${jsonPath}`);

    // Quality gates
    const baseline = report.suites.ablation.configs.find(
      (c) => c.config.name === report.suites.ablation.baselineName
    );
    expect(baseline).toBeDefined();
    expect(baseline!.avgRecall).toBeGreaterThan(0.5);
    expect(baseline!.avgMrr).toBeGreaterThan(0.5);

    // Scalability: recall should stay above 30% even at max scale
    const maxScale = report.suites.scalability.dataPoints.at(-1);
    expect(maxScale).toBeDefined();
    expect(maxScale!.avgRecall).toBeGreaterThan(0.3);

    // Sanity: no NaN values in ablation
    for (const cr of report.suites.ablation.configs) {
      expect(Number.isFinite(cr.avgPrecision)).toBe(true);
      expect(Number.isFinite(cr.avgRecall)).toBe(true);
      expect(Number.isFinite(cr.avgMrr)).toBe(true);
      expect(Number.isFinite(cr.avgNdcg)).toBe(true);
    }

    // Sanity: latency profile has positive values
    expect(report.suites.latencyProfile.coldStartMs).toBeGreaterThan(0);
    expect(report.suites.latencyProfile.search.p50).toBeGreaterThan(0);
  });
});

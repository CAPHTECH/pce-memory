/**
 * Generate a publishable Markdown benchmark report.
 *
 * Pure function: BenchmarkReport → string.
 */

import type { BenchmarkReport, LatencyStats } from '../types';

function pct(v: number): string {
  return `${(v * 100).toFixed(1)}%`;
}

function ms(v: number): string {
  return `${v.toFixed(1)}ms`;
}

function delta(v: number): string {
  const sign = v >= 0 ? '+' : '';
  return `${sign}${(v * 100).toFixed(1)}pp`;
}

function latencyRow(label: string, stats: LatencyStats): string {
  return `| ${label} | ${ms(stats.p50)} | ${ms(stats.p95)} | ${ms(stats.p99)} | ${ms(stats.mean)} |`;
}

export function generateMarkdownReport(report: BenchmarkReport): string {
  const { ablation, scalability, latencyProfile } = report.suites;
  const lines: string[] = [];

  // Header
  lines.push('# pce-memory Benchmark Report');
  lines.push('');
  lines.push(
    `> Generated: ${report.timestamp} | Version: ${report.version} | Model: ${report.environment.embeddingModel} (${report.environment.embeddingDim}-dim) | Node: ${report.environment.node} | Platform: ${report.environment.platform}`,
  );
  lines.push('');

  // Executive Summary
  const baseline = ablation.configs.find((c) => c.config.name === ablation.baselineName);
  const textOnly = ablation.configs.find((c) => c.config.name === 'text-only');
  const vectorOnly = ablation.configs.find((c) => c.config.name === 'vector-only');
  const scale5k = scalability.dataPoints.find((d) => d.claimCount === 5000);
  const scale15 = scalability.dataPoints.find((d) => d.claimCount === 15);

  lines.push('## Executive Summary');
  lines.push('');
  if (baseline && textOnly && vectorOnly) {
    lines.push(
      `- **Hybrid search** achieves ${pct(baseline.avgRecall)} recall, outperforming text-only (${pct(textOnly.avgRecall)}) and vector-only (${pct(vectorOnly.avgRecall)})`,
    );
    lines.push(
      `- **g() reranking** improves nDCG by ${delta(baseline.avgNdcg - (ablation.configs.find((c) => c.config.name === 'hybrid-no-rerank')?.avgNdcg ?? 0))} over hybrid without reranking`,
    );
  }
  if (scale5k && scale15) {
    lines.push(
      `- **Scalability**: recall degrades from ${pct(scale15.avgRecall)} (15 claims) to ${pct(scale5k.avgRecall)} (5,000 claims), with p50 latency at ${ms(scale5k.latency.p50)}`,
    );
  }
  lines.push(`- **Search latency**: p50 = ${ms(latencyProfile.search.p50)}, p95 = ${ms(latencyProfile.search.p95)}`);
  lines.push('');

  // 1. Ablation Study
  lines.push('## 1. Ablation Study');
  lines.push('');
  lines.push('Measures the contribution of each search component by systematically toggling features.');
  lines.push('');
  lines.push('| Config | Alpha | kText | kVec | Rerank | MMR | Precision@10 | Recall@10 | MRR | nDCG | Latency |');
  lines.push('|--------|-------|-------|------|--------|-----|-------------|-----------|-----|------|---------|');
  for (const cr of ablation.configs) {
    const c = cr.config;
    lines.push(
      `| ${c.name === ablation.baselineName ? `**${c.name}**` : c.name} | ${c.alpha} | ${c.kText} | ${c.kVec} | ${c.enableRerank ? 'on' : 'off'} | ${c.mmr.enabled ? 'on' : 'off'} | ${pct(cr.avgPrecision)} | ${pct(cr.avgRecall)} | ${pct(cr.avgMrr)} | ${pct(cr.avgNdcg)} | ${ms(cr.avgLatencyMs)} |`,
    );
  }
  lines.push('');

  // Delta table
  lines.push('### Delta from Baseline');
  lines.push('');
  lines.push('| Config | \u0394Precision | \u0394Recall | \u0394MRR | \u0394nDCG |');
  lines.push('|--------|-----------|--------|------|-------|');
  for (const d of ablation.deltas) {
    lines.push(
      `| ${d.configName} | ${delta(d.deltaPrecision)} | ${delta(d.deltaRecall)} | ${delta(d.deltaMrr)} | ${delta(d.deltaNdcg)} |`,
    );
  }
  lines.push('');

  // 2. Scalability
  lines.push('## 2. Scalability');
  lines.push('');
  lines.push('Measures search quality and latency as the knowledge base grows (baseline config: hybrid + rerank).');
  lines.push('');
  lines.push('| Claims | Precision@10 | Recall@10 | MRR | nDCG | Latency p50 | Latency p95 |');
  lines.push('|--------|-------------|-----------|-----|------|-------------|-------------|');
  for (const dp of scalability.dataPoints) {
    lines.push(
      `| ${dp.claimCount.toLocaleString()} | ${pct(dp.avgPrecision)} | ${pct(dp.avgRecall)} | ${pct(dp.avgMrr)} | ${pct(dp.avgNdcg)} | ${ms(dp.latency.p50)} | ${ms(dp.latency.p95)} |`,
    );
  }
  lines.push('');

  // 3. Latency Profile
  lines.push('## 3. Latency Profile');
  lines.push('');
  lines.push(`| Operation | Time |`);
  lines.push(`|-----------|------|`);
  lines.push(`| Embedding model cold start | ${ms(latencyProfile.coldStartMs)} |`);
  lines.push(`| Embedding (first call) | ${ms(latencyProfile.embedding.coldMs)} |`);
  lines.push(`| Embedding (cached) | ${ms(latencyProfile.embedding.warmMs)} |`);
  lines.push(`| Rerank overhead (mean) | ${ms(latencyProfile.rerankOverhead.overheadMs)} |`);
  lines.push('');
  lines.push('### Search Latency Distribution');
  lines.push('');
  lines.push('| Config | p50 | p95 | p99 | Mean |');
  lines.push('|--------|-----|-----|-----|------|');
  lines.push(latencyRow('With rerank', latencyProfile.rerankOverhead.withRerank));
  lines.push(latencyRow('Without rerank', latencyProfile.rerankOverhead.withoutRerank));
  lines.push('');

  // Methodology
  lines.push('## Methodology');
  lines.push('');
  lines.push(`- **Embedding model**: ${report.environment.embeddingModel} (${report.environment.embeddingDim}-dim, local ONNX)`);
  lines.push('- **Database**: DuckDB in-memory');
  const queryCount = report.suites.ablation.configs[0]?.perQuery.length ?? 0;
  lines.push(`- **Test corpus**: ${queryCount} golden queries across 7 categories (exact match, paraphrase, multi-hop, hard-negative discrimination)`);
  lines.push('- **Claims**: 15 golden claims (10 positive + 5 hard negatives) + synthetic noise claims for scalability');
  lines.push('- **IR Metrics**: Precision@k, Recall@k, MRR, nDCG computed via assay-kit `evaluateRetrieval()`');
  lines.push('- **Latency**: `performance.now()` high-resolution timer, 20 repetitions for percentile calculation');
  lines.push('- **Scalability**: 3 repetitions per scale point for latency stability');
  lines.push('');

  return lines.join('\n');
}

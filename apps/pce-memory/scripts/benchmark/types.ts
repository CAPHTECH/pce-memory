/**
 * Benchmark evaluation types for pce-memory.
 */

import type { ActivateIntent } from '../../src/domain/types';

// ---------------------------------------------------------------------------
// Latency
// ---------------------------------------------------------------------------

export interface LatencyStats {
  p50: number;
  p95: number;
  p99: number;
  mean: number;
  min: number;
  max: number;
}

export function computeLatencyStats(samples: number[]): LatencyStats {
  if (samples.length === 0) {
    return { p50: 0, p95: 0, p99: 0, mean: 0, min: 0, max: 0 };
  }
  const sorted = [...samples].sort((a, b) => a - b);
  const percentile = (p: number) => sorted[Math.min(Math.floor(sorted.length * p), sorted.length - 1)]!;
  const mean = sorted.reduce((a, b) => a + b, 0) / sorted.length;
  return {
    p50: percentile(0.5),
    p95: percentile(0.95),
    p99: percentile(0.99),
    mean,
    min: sorted[0]!,
    max: sorted[sorted.length - 1]!,
  };
}

// ---------------------------------------------------------------------------
// Ablation
// ---------------------------------------------------------------------------

export interface AblationConfig {
  name: string;
  alpha: number;
  kText: number;
  kVec: number;
  enableRerank: boolean;
  mmr: { enabled: boolean; lambda?: number };
  intent?: ActivateIntent;
}

export interface QueryMetrics {
  queryId: string;
  precision: number;
  recall: number;
  mrr: number;
  ndcg: number;
  latencyMs: number;
}

export interface AblationConfigResult {
  config: AblationConfig;
  avgPrecision: number;
  avgRecall: number;
  avgMrr: number;
  avgNdcg: number;
  avgLatencyMs: number;
  perQuery: QueryMetrics[];
}

export interface AblationDelta {
  configName: string;
  deltaPrecision: number;
  deltaRecall: number;
  deltaMrr: number;
  deltaNdcg: number;
}

export interface AblationResult {
  configs: AblationConfigResult[];
  baselineName: string;
  deltas: AblationDelta[];
}

// ---------------------------------------------------------------------------
// Scalability
// ---------------------------------------------------------------------------

export interface ScalabilityDataPoint {
  claimCount: number;
  avgPrecision: number;
  avgRecall: number;
  avgMrr: number;
  avgNdcg: number;
  latency: LatencyStats;
}

export interface ScalabilityResult {
  dataPoints: ScalabilityDataPoint[];
}

// ---------------------------------------------------------------------------
// Latency Profile
// ---------------------------------------------------------------------------

export interface LatencyProfileResult {
  coldStartMs: number;
  embedding: {
    coldMs: number;
    warmMs: number;
  };
  search: LatencyStats;
  rerankOverhead: {
    withRerank: LatencyStats;
    withoutRerank: LatencyStats;
    overheadMs: number;
  };
}

// ---------------------------------------------------------------------------
// Top-level Report
// ---------------------------------------------------------------------------

export interface BenchmarkEnvironment {
  node: string;
  platform: string;
  embeddingModel: string;
  embeddingDim: number;
}

export interface BenchmarkReport {
  timestamp: string;
  version: string;
  environment: BenchmarkEnvironment;
  suites: {
    ablation: AblationResult;
    scalability: ScalabilityResult;
    latencyProfile: LatencyProfileResult;
  };
}

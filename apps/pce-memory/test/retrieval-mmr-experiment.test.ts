import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import type { HybridSearchConfig } from '../src/store/hybridSearch';
import { hybridSearchWithScores } from '../src/store/hybridSearch';
import {
  cleanupPrecisionBenchmarkDb,
  createLookupEmbeddingService,
  measureTopK,
  resetPrecisionBenchmarkDb,
  runMeasuredSearch,
  seedBenchmarkClaim,
} from '../../../validation/precision-experiments/harness';

describe('retrieval precision experiment: MMR diversification', () => {
  let dbPath = '';

  beforeEach(async () => {
    dbPath = await resetPrecisionBenchmarkDb();
  });

  afterEach(async () => {
    await cleanupPrecisionBenchmarkDb(dbPath);
  });

  it('improves precision and diversity on duplicate-heavy candidate pools', async () => {
    const query = 'authentication controls';
    const embeddingService = createLookupEmbeddingService(
      {
        [query]: [1, 0, 0],
      },
      [0.25, 0.25, 0.25]
    );

    const a1 = await seedBenchmarkClaim({
      text: 'authentication controls jwt key rotation checklist primary',
      content_hash: 'sha256:mmr-a1',
      critic: 4.9,
      embedding: [1, 0, 0],
    });
    const a2 = await seedBenchmarkClaim({
      text: 'authentication controls jwt key rotation checklist duplicate one',
      content_hash: 'sha256:mmr-a2',
      critic: 4.8,
      embedding: [0.99, 0.01, 0],
    });
    const a3 = await seedBenchmarkClaim({
      text: 'authentication controls jwt key rotation checklist duplicate two',
      content_hash: 'sha256:mmr-a3',
      critic: 4.7,
      embedding: [0.98, 0.02, 0],
    });
    const b1 = await seedBenchmarkClaim({
      text: 'authentication controls session fixation mitigation checklist',
      content_hash: 'sha256:mmr-b1',
      critic: 4.5,
      embedding: [0.82, 0.57, 0],
    });
    const c1 = await seedBenchmarkClaim({
      text: 'authentication controls refresh token replay prevention checklist',
      content_hash: 'sha256:mmr-c1',
      critic: 4.35,
      embedding: [0.79, 0, 0.61],
    });
    await seedBenchmarkClaim({
      text: 'authentication controls ui wording cleanup note',
      content_hash: 'sha256:mmr-noise',
      critic: 4.0,
      embedding: [0.97, 0.03, 0],
    });

    const clusterByClaimId: Record<string, string> = {
      [a1]: 'jwt-rotation',
      [a2]: 'jwt-rotation',
      [a3]: 'jwt-rotation',
      [b1]: 'session-fixation',
      [c1]: 'token-replay',
    };
    const relevantIds = [a1, b1, c1];

    const baseConfig: Partial<HybridSearchConfig> = {
      embeddingService,
      includeBreakdown: true,
      enableRerank: true,
    };

    const baselineRun = await runMeasuredSearch(() =>
      hybridSearchWithScores(['project'], 3, query, baseConfig)
    );
    const diversifiedRun = await runMeasuredSearch(() =>
      hybridSearchWithScores(['project'], 3, query, {
        ...baseConfig,
        mmr: {
          enabled: true,
          lambda: 0.35,
          maxCandidates: 6,
        },
      })
    );

    const baselineMetrics = measureTopK(
      baselineRun.results,
      relevantIds,
      clusterByClaimId,
      baselineRun.avgLatencyMs
    );
    const diversifiedMetrics = measureTopK(
      diversifiedRun.results,
      relevantIds,
      clusterByClaimId,
      diversifiedRun.avgLatencyMs
    );

    if (process.env['PRINT_PRECISION_METRICS'] === '1') {
      console.log(
        JSON.stringify({
          idea: 'mmr',
          baseline: baselineMetrics,
          variant: diversifiedMetrics,
        })
      );
    }

    expect(baselineMetrics.top_ids.slice(0, 3)).toEqual([a1, a2, a3]);
    expect(diversifiedMetrics.precision).toBeGreaterThan(baselineMetrics.precision);
    expect(diversifiedMetrics.recall).toBeGreaterThan(baselineMetrics.recall);
    expect(diversifiedMetrics.diversity).toBeGreaterThan(baselineMetrics.diversity);
    expect(diversifiedMetrics.precision).toBeGreaterThanOrEqual(2 / 3);
    expect(diversifiedMetrics.diversity).toBeGreaterThanOrEqual(2);
  });
});

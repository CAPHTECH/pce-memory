import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import type { HybridSearchConfig } from '../src/store/hybridSearch';
import { hybridSearchWithScores } from '../src/store/hybridSearch';
import { recordFeedback } from '../src/store/feedback';
import {
  cleanupPrecisionBenchmarkDb,
  measureTopK,
  resetPrecisionBenchmarkDb,
  runMeasuredSearch,
  seedBenchmarkClaim,
} from './helpers/precisionBenchmarkTestUtils';

describe('retrieval precision experiment: feedback-aware boost', () => {
  let dbPath = '';

  const runWithPreparedStatementRetry = async (fn: () => Promise<void>, retries = 3) => {
    for (let attempt = 1; attempt <= retries; attempt++) {
      try {
        await fn();
        return;
      } catch (error) {
        if (
          attempt === retries ||
          !(error instanceof Error) ||
          !error.message.includes('Failed to execute prepared statement')
        ) {
          throw error;
        }
        await new Promise((resolve) => setTimeout(resolve, 50 * attempt));
      }
    }
  };

  beforeEach(async () => {
    dbPath = await resetPrecisionBenchmarkDb();
  });

  afterEach(async () => {
    await cleanupPrecisionBenchmarkDb(dbPath);
  });

  it('promotes repeatedly helpful claims over higher-critic harmful ones', async () => {
    await runWithPreparedStatementRetry(async () => {
      const helpful1 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery with verified production steps',
        content_hash: 'sha256:fbexp-helpful-1',
        critic: 3.95,
      });
      const helpful2 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery covering schema and cache revert',
        content_hash: 'sha256:fbexp-helpful-2',
        critic: 3.9,
      });
      const helpful3 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery with operator signoff sequence',
        content_hash: 'sha256:fbexp-helpful-3',
        critic: 3.85,
      });

      const harmful1 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery but missing safety gates',
        content_hash: 'sha256:fbexp-harmful-1',
        critic: 4.2,
      });
      const harmful2 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery with stale assumptions',
        content_hash: 'sha256:fbexp-harmful-2',
        critic: 4.15,
      });
      const harmful3 = await seedBenchmarkClaim({
        text: 'rollback checklist for incident recovery with unverified shortcuts',
        content_hash: 'sha256:fbexp-harmful-3',
        critic: 4.1,
      });

      for (const claimId of [helpful1, helpful2, helpful3]) {
        await recordFeedback({ claim_id: claimId, signal: 'helpful' });
      }
      for (const claimId of [harmful1, harmful2, harmful3]) {
        await recordFeedback({ claim_id: claimId, signal: 'harmful' });
      }

      const relevantIds = [helpful1, helpful2, helpful3];
      const clusterByClaimId: Record<string, string> = {
        [helpful1]: 'verified-steps',
        [helpful2]: 'cache-revert',
        [helpful3]: 'operator-signoff',
        [harmful1]: 'missing-gates',
        [harmful2]: 'stale-assumptions',
        [harmful3]: 'shortcuts',
      };
      const query = 'rollback checklist incident recovery';
      const baseConfig: Partial<HybridSearchConfig> = {
        enableRerank: true,
        includeBreakdown: true,
      };

      const baselineRun = await runMeasuredSearch(() =>
        hybridSearchWithScores(['project'], 3, query, baseConfig)
      );
      const boostedRun = await runMeasuredSearch(() =>
        hybridSearchWithScores(['project'], 3, query, {
          ...baseConfig,
          feedbackBoost: {
            enabled: true,
            helpfulWeight: 0.25,
            harmfulWeight: 0.35,
            outdatedWeight: 0.18,
            duplicateWeight: 0.12,
            minMultiplier: 0.45,
            maxMultiplier: 1.65,
          },
        })
      );

      const baselineMetrics = measureTopK(
        baselineRun.results,
        relevantIds,
        clusterByClaimId,
        baselineRun.avgLatencyMs
      );
      const boostedMetrics = measureTopK(
        boostedRun.results,
        relevantIds,
        clusterByClaimId,
        boostedRun.avgLatencyMs
      );

      if (process.env['PRINT_PRECISION_METRICS'] === '1') {
        console.log(
          JSON.stringify({
            idea: 'feedback_boost',
            baseline: baselineMetrics,
            variant: boostedMetrics,
          })
        );
      }

      expect(boostedMetrics.precision).toBeGreaterThan(baselineMetrics.precision);
      expect(boostedMetrics.recall).toBeGreaterThan(baselineMetrics.recall);
      expect(boostedMetrics.precision).toBe(1);
      expect(boostedMetrics.recall).toBe(1);
    });
  });
});

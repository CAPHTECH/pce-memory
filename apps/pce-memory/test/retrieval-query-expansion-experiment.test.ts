import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import type { HybridSearchConfig } from '../src/store/hybridSearch';
import { hybridSearchWithScores } from '../src/store/hybridSearch';
import { linkClaimEntity, upsertEntity } from '../src/store/entities';
import { upsertRelation } from '../src/store/relations';
import {
  cleanupPrecisionBenchmarkDb,
  measureTopK,
  resetPrecisionBenchmarkDb,
  runMeasuredSearch,
  seedBenchmarkClaim,
} from '../../../validation/precision-experiments/harness';

describe('retrieval precision experiment: entity graph query expansion', () => {
  let dbPath = '';

  beforeEach(async () => {
    dbPath = await resetPrecisionBenchmarkDb();
  });

  afterEach(async () => {
    await cleanupPrecisionBenchmarkDb(dbPath);
  });

  it('recovers relevant claims that only become lexical matches after graph expansion', async () => {
    const authEntity = await upsertEntity({
      id: 'ent_auth',
      type: 'Concept',
      name: 'Authentication',
      canonical_key: 'authentication',
    });
    const jwtEntity = await upsertEntity({
      id: 'ent_jwt',
      type: 'Concept',
      name: 'JWT',
      canonical_key: 'jwt',
    });
    const sessionEntity = await upsertEntity({
      id: 'ent_session',
      type: 'Concept',
      name: 'Session',
      canonical_key: 'session',
    });
    const refreshEntity = await upsertEntity({
      id: 'ent_refresh',
      type: 'Concept',
      name: 'Refresh Token',
      canonical_key: 'refresh-token',
    });

    await upsertRelation({
      id: 'rel_auth_jwt',
      src_id: authEntity.id,
      dst_id: jwtEntity.id,
      type: 'USES',
    });
    await upsertRelation({
      id: 'rel_auth_session',
      src_id: authEntity.id,
      dst_id: sessionEntity.id,
      type: 'USES',
    });
    await upsertRelation({
      id: 'rel_auth_refresh',
      src_id: authEntity.id,
      dst_id: refreshEntity.id,
      type: 'USES',
    });

    const jwtClaim = await seedBenchmarkClaim({
      text: 'JWT rotation prevents token leakage during key rollover',
      content_hash: 'sha256:qexp-jwt',
      critic: 4.9,
    });
    const sessionClaim = await seedBenchmarkClaim({
      text: 'Session idle timeout reduces stale token exposure after signout',
      content_hash: 'sha256:qexp-session',
      critic: 4.8,
    });
    const refreshClaim = await seedBenchmarkClaim({
      text: 'Refresh token family revocation stops replay after credential theft',
      content_hash: 'sha256:qexp-refresh',
      critic: 4.7,
    });

    await linkClaimEntity(jwtClaim, jwtEntity.id);
    await linkClaimEntity(sessionClaim, sessionEntity.id);
    await linkClaimEntity(refreshClaim, refreshEntity.id);

    await seedBenchmarkClaim({
      text: 'authentication meeting notes for stakeholder scheduling',
      content_hash: 'sha256:qexp-noise-1',
      critic: 4.3,
    });
    await seedBenchmarkClaim({
      text: 'authentication slide deck copy review',
      content_hash: 'sha256:qexp-noise-2',
      critic: 4.2,
    });
    await seedBenchmarkClaim({
      text: 'authentication roadmap placeholder for next quarter',
      content_hash: 'sha256:qexp-noise-3',
      critic: 4.1,
    });

    const relevantIds = [jwtClaim, sessionClaim, refreshClaim];
    const clusterByClaimId: Record<string, string> = {
      [jwtClaim]: 'jwt',
      [sessionClaim]: 'session',
      [refreshClaim]: 'refresh',
    };
    const query = 'authentication';
    const baseConfig: Partial<HybridSearchConfig> = {
      enableRerank: false,
      includeBreakdown: true,
    };

    const baselineRun = await runMeasuredSearch(() =>
      hybridSearchWithScores(['project'], 3, query, baseConfig)
    );
    const expandedRun = await runMeasuredSearch(() =>
      hybridSearchWithScores(['project'], 3, query, {
        ...baseConfig,
        queryExpansion: {
          enabled: true,
          maxSeedEntities: 1,
          maxRelatedEntities: 4,
          maxExpansionTerms: 4,
        },
      })
    );

    const baselineMetrics = measureTopK(
      baselineRun.results,
      relevantIds,
      clusterByClaimId,
      baselineRun.avgLatencyMs
    );
    const expandedMetrics = measureTopK(
      expandedRun.results,
      relevantIds,
      clusterByClaimId,
      expandedRun.avgLatencyMs
    );

    if (process.env['PRINT_PRECISION_METRICS'] === '1') {
      console.log(
        JSON.stringify({
          idea: 'query_expansion',
          baseline: baselineMetrics,
          variant: expandedMetrics,
        })
      );
    }

    expect(baselineMetrics.precision).toBe(0);
    expect(baselineMetrics.recall).toBe(0);
    expect(expandedMetrics.precision).toBeGreaterThan(baselineMetrics.precision);
    expect(expandedMetrics.recall).toBeGreaterThan(baselineMetrics.recall);
    expect(expandedMetrics.precision).toBe(1);
    expect(expandedMetrics.recall).toBe(1);
    expect(expandedMetrics.diversity).toBe(3);
  });
});

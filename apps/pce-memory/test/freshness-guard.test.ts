import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { insertPromotionQueueRow } from '../src/store/promotionQueue';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { initRateState, resetRates } from '../src/store/rate';
import { setEmbeddingService } from '../src/store/hybridSearch';

beforeEach(async () => {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

function createLookupEmbeddingService(
  lookup: Record<string, readonly number[]>,
  fallback: readonly number[] = [0, 1]
): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      () =>
        Promise.resolve(
          E.right({
            embedding: lookup[text] ?? fallback,
            modelVersion: 'freshness-guard-test-v1',
          })
        ),
  };
}

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

async function applyPolicy() {
  expectSuccess(await dispatchTool('pce_memory_policy_apply', {}));
}

async function upsertProjectClaim(text: string, provenanceAt: string) {
  const payload = expectSuccess(
    await dispatchTool('pce_memory_upsert', {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: { at: provenanceAt, actor: 'vitest' },
    })
  );
  return payload.id as string;
}

async function updateClaimTimestamps(claimId: string, createdAt: string) {
  const conn = await getConnection();
  await conn.run(
    'UPDATE claims SET created_at = $1, updated_at = $1, recency_anchor = $1 WHERE id = $2',
    [createdAt, claimId]
  );
}

describe('knowledge freshness guard', () => {
  it('upsert returns similar_existing for nearby active claims in the same scope', async () => {
    const existingText = 'Warehouse routing timeout is 15 seconds for service maple.';
    const similarText = 'Warehouse routing timeout is 25 seconds for service maple after update.';
    setEmbeddingService(
      createLookupEmbeddingService({
        [existingText]: [1, 0],
        [similarText]: [0.9, 0.4358898943540673],
      })
    );

    await applyPolicy();

    const existingId = await upsertProjectClaim(existingText, '2025-01-01T00:00:00.000Z');
    const result = expectSuccess(
      await dispatchTool('pce_memory_upsert', {
        text: similarText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        content_hash: `sha256:${computeContentHash(similarText)}`,
        provenance: { at: '2025-01-02T00:00:00.000Z', actor: 'vitest' },
      })
    );

    expect(result.similar_existing).toEqual([
      expect.objectContaining({
        id: existingId,
        similarity: expect.any(Number),
        created_at: expect.any(String),
      }),
    ]);
    expect((result.similar_existing as Array<{ similarity: number }>)[0]?.similarity).toBeGreaterThan(
      0.85
    );
  });

  it('promote returns similar_existing for nearby durable claims', async () => {
    const existingText = 'Ingress cache TTL is 30 seconds for workspace cedar.';
    const promotedText = 'Ingress cache TTL is 45 seconds for workspace cedar after the review.';
    setEmbeddingService(
      createLookupEmbeddingService({
        [existingText]: [1, 0],
        [promotedText]: [0.9, 0.4358898943540673],
      })
    );

    await applyPolicy();

    const existingId = await upsertProjectClaim(existingText, '2025-01-01T00:00:00.000Z');

    await insertPromotionQueueRow({
      id: 'pq_freshness_guard',
      source_layer: 'micro',
      target_layer: 'meso',
      source_ids: '[]',
      distilled_text: promotedText,
      candidate_hash: `sha256:${computeContentHash(promotedText)}`,
      proposed_kind: 'fact',
      proposed_scope: 'project',
      proposed_boundary_class: 'internal',
      proposed_memory_type: 'knowledge',
      provenance: JSON.stringify({ source_observation_ids: [], source_claim_ids: [] }),
      evidence_ids: '[]',
      created_at: '2025-01-03T00:00:00.000Z',
    });

    const promote = expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: 'pq_freshness_guard',
        provenance: { at: '2025-01-03T00:00:00.000Z', actor: 'vitest' },
      })
    );

    expect(promote.similar_existing).toEqual([
      expect.objectContaining({
        id: existingId,
        similarity: expect.any(Number),
      }),
    ]);
  });

  it('activate annotates stale candidates when a newer similar claim exists', async () => {
    const staleText = 'Service maple timeout is 15 seconds under the rollout policy.';
    const freshText = 'Service maple timeout is 25 seconds after the rollout update.';
    const distractorText = 'Vendor routing memo keeps pallet threshold at 70 units.';
    const queryText = 'service maple timeout rollout policy';
    setEmbeddingService(
      createLookupEmbeddingService({
        [staleText]: [1, 0],
        [freshText]: [0.92, 0.39191835884530846],
        [distractorText]: [0, 1],
        [queryText]: [1, 0],
      })
    );

    await applyPolicy();

    const staleId = await upsertProjectClaim(staleText, '2025-01-01T00:00:00.000Z');
    const freshId = await upsertProjectClaim(freshText, '2025-01-02T00:00:00.000Z');
    await upsertProjectClaim(distractorText, '2025-01-02T00:00:00.000Z');

    await updateClaimTimestamps(staleId, '2025-01-01T00:00:00.000Z');
    await updateClaimTimestamps(freshId, '2025-01-02T00:00:00.000Z');

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: queryText,
        top_k: 3,
      })
    );

    const claims = activate.claims as Array<{
      claim: { id: string; freshness?: string; newer_similar?: string };
      rank: number;
    }>;
    const staleResult = claims.find((item) => item.claim.id === staleId);
    const freshResult = claims.find((item) => item.claim.id === freshId);

    expect(staleResult?.claim.freshness).toBe('stale_candidate');
    expect(staleResult?.claim.newer_similar).toBe(freshId);
    expect(freshResult?.claim.freshness).toBeUndefined();
    expect((freshResult?.rank ?? Number.POSITIVE_INFINITY)).toBeLessThan(
      staleResult?.rank ?? Number.POSITIVE_INFINITY
    );
  });
});

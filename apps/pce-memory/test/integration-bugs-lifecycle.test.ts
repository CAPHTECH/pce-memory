/**
 * Integration Bug Hunt Tests — APPROACH 1: Full Lifecycle Stress
 *
 * Split from integration-bugs.test.ts
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';
import {
  applyPolicy,
  expectSuccess,
  observeRaw,
  distillFromObservations,
  promoteCandidate,
  activateClaims,
  submitFeedback,
  rollbackClaim,
  countClaims,
  countActiveClaims,
  countObservations,
  countPromotionQueue,
  countFeedback,
} from './helpers/integrationBugsTestUtils';

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

// ============================================================
// APPROACH 1: Full Lifecycle Stress
// ============================================================

describe('APPROACH 1: Full Lifecycle Stress', () => {
  it('10 sequential full lifecycles with DB consistency checks', async () => {
    await applyPolicy();

    const claimIds: string[] = [];
    const rollbackIds: string[] = [];

    for (let i = 0; i < 10; i++) {
      // observe
      const obs = await observeRaw(`lifecycle stress iteration ${i} unique content marker`);
      expect(obs.observation_id).toMatch(/^obs_/);

      // distill
      const distill = await distillFromObservations([obs.observation_id]);
      expect(distill.candidate_id).toMatch(/^pq_/);
      expect(distill.status).toBe('pending');

      // promote
      const promote = await promoteCandidate(distill.candidate_id);
      expect(promote.claim_id).toMatch(/^clm_/);
      expect(promote.is_new).toBe(true);
      claimIds.push(promote.claim_id);

      // activate
      const activated = await activateClaims(`lifecycle stress iteration ${i}`);
      expect(activated.claims_count).toBeGreaterThanOrEqual(1);
      expect(activated.claims.some((c) => c.claim.id === promote.claim_id)).toBe(true);

      // feedback
      const feedback = await submitFeedback(promote.claim_id, 'helpful');
      expect(feedback.signal).toBe('helpful');

      // rollback
      const rb = await rollbackClaim(promote.claim_id, `rollback iteration ${i}`);
      expect(rb.superseded_claim_id).toBe(promote.claim_id);
      rollbackIds.push(rb.rollback_id);

      // verify claim is no longer retrievable
      const afterRb = await activateClaims(`lifecycle stress iteration ${i}`);
      const idsAfter = afterRb.claims.map((c) => c.claim.id);
      expect(idsAfter).not.toContain(promote.claim_id);
    }

    // DB consistency: all claims created, all rolled back
    const totalClaims = await countClaims();
    expect(totalClaims).toBe(10);

    const activeClaims = await countActiveClaims();
    expect(activeClaims).toBe(0);

    // observations should all exist
    const totalObs = await countObservations();
    expect(totalObs).toBe(10);

    // promotion queue: 10 distill (pending->accepted) + 10 rollback
    const totalPQ = await countPromotionQueue();
    expect(totalPQ).toBe(20);

    // feedback entries
    const totalFeedback = await countFeedback();
    expect(totalFeedback).toBe(10);
  });

  it('rapid upsert + activate cycling preserves correct claim count', async () => {
    await applyPolicy();

    // Upsert 20 distinct claims rapidly
    const ids: string[] = [];
    for (let i = 0; i < 20; i++) {
      const result = expectSuccess<{ id: string }>(
        await upsertClaimViaTool({
          text: `rapid cycle claim number ${i} with unique text`,
          kind: 'fact',
          scope: 'project',
        })
      );
      ids.push(result.id);
    }

    // Activate should find claims
    const activated = await activateClaims('rapid cycle claim', { top_k: 50 });
    expect(activated.claims_count).toBeGreaterThan(0);
    expect(activated.claims_count).toBeLessThanOrEqual(50);

    // DB consistency
    const total = await countClaims();
    expect(total).toBe(20);
    const active = await countActiveClaims();
    expect(active).toBe(20);
  });
});

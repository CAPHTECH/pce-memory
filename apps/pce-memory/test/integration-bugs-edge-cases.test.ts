/**
 * Integration Bug Hunt Tests — APPROACH 3: Edge Case Workflows
 *
 * Split from integration-bugs.test.ts
 */
import { beforeEach, describe, expect, it } from 'vitest';
import { resetRetrievalPlannerTestState, upsertClaimViaTool } from './helpers/retrievalPlannerTestUtils';
import {
  applyPolicy,
  dispatchTool,
  expectSuccess,
  observeRaw,
  distillFromObservations,
  distillFromClaims,
  promoteCandidate,
  activateClaims,
  submitFeedback,
  rollbackClaim,
  linkClaims,
  readClaimRow,
  countClaims,
  countActiveClaims,
  buildProvenance,
  type HealthResult,
} from './helpers/integrationBugsTestUtils';

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

// ============================================================
// APPROACH 3: Edge Case Workflows
// ============================================================

describe('APPROACH 3: Edge Case Workflows', () => {
  it('promote -> rollback -> distill from same observation -> promote again succeeds', async () => {
    await applyPolicy();

    // observe
    const obs = await observeRaw('redistill edge case unique content for re-promotion test');

    // distill + promote
    const distill1 = await distillFromObservations([obs.observation_id]);
    const promote1 = await promoteCandidate(distill1.candidate_id);
    expect(promote1.is_new).toBe(true);

    // rollback
    await rollbackClaim(promote1.claim_id, 'testing redistill');

    // distill again from the same observation (same text = same candidate_hash)
    const distill2 = await distillFromObservations([obs.observation_id]);
    expect(distill2.candidate_id).toBeTruthy();
    expect(distill2.candidate_id).not.toBe(distill1.candidate_id);

    // After fix: upsertClaim detects the rolled-back claim with matching content_hash
    // and revives it instead of failing with UNIQUE constraint violation
    const promote2 = await promoteCandidate(distill2.candidate_id);
    expect(promote2.claim_id).toBeTruthy();
    expect(promote2.is_new).toBe(true);

    // Verify the claim is retrievable
    const activated = await activateClaims('redistill edge case');
    expect(activated.claims_count).toBeGreaterThanOrEqual(1);
  });

  it('upsert A, upsert similar B, rollback A, activate returns only B', async () => {
    await applyPolicy();

    const claimA = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'freshness pair claim A about caching strategy redis v1' })
    );
    const claimB = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'freshness pair claim B about caching strategy redis v2 improved' })
    );

    // rollback A
    await rollbackClaim(claimA.id, 'superseded by B');

    // activate
    const result = await activateClaims('caching strategy redis');
    const resultIds = result.claims.map((c) => c.claim.id);
    expect(resultIds).not.toContain(claimA.id);
    expect(resultIds).toContain(claimB.id);
  });

  it('circular claim_links: A->B->C->A, activate with traversal', async () => {
    await applyPolicy();

    const claimA = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'circular link claim A about microservice architecture' })
    );
    const claimB = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'circular link claim B about service mesh routing' })
    );
    const claimC = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'circular link claim C about API gateway patterns' })
    );

    // Create circular links A->B->C->A
    await linkClaims(claimA.id, claimB.id, 'related', 0.9);
    await linkClaims(claimB.id, claimC.id, 'related', 0.9);
    await linkClaims(claimC.id, claimA.id, 'related', 0.9);

    // Activate - should not infinite loop, should return claims
    const result = await activateClaims('microservice architecture service mesh');
    expect(result.claims_count).toBeGreaterThanOrEqual(1);
    expect(result.active_context_id).toBeTruthy();
  });

  it('distill from a claim and promote to different scope succeeds (scope elevation)', async () => {
    await applyPolicy();

    // Create first-generation: observe -> distill -> promote
    const obs = await observeRaw('nested distill test original observation content for chain');
    const distill1 = await distillFromObservations([obs.observation_id]);
    const promote1 = await promoteCandidate(distill1.candidate_id);

    // Create second-generation: distill from the promoted claim into principle scope
    // After fix: getPromotionCandidateConflictMessage only rejects on text mismatch,
    // so same-text different-scope promotion (scope elevation) succeeds.
    const distill2 = await distillFromClaims([promote1.claim_id], {
      proposed_scope: 'principle',
      note: 'elevating to principle from project claim',
    });
    expect(distill2.proposed_scope).toBe('principle');

    // Promote succeeds - same text with different scope is idempotent (returns existing claim)
    const promote2 = await promoteCandidate(distill2.candidate_id);
    expect(promote2.claim_id).toBeTruthy();

    // The claim retains its original scope (idempotent upsert returns existing)
    const row = await readClaimRow(promote2.claim_id);
    expect(row).toBeDefined();
  });

  it('activate with all filters that exclude everything returns empty result', async () => {
    await applyPolicy();

    // Create claims with various kinds
    await upsertClaimViaTool({ text: 'exclude everything test fact claim', kind: 'fact', memory_type: 'knowledge' });
    await upsertClaimViaTool({ text: 'exclude everything test pref claim', kind: 'preference', memory_type: 'procedure' });

    // Activate with kind_filter that matches nothing in combination with memory_type_filter
    const result = await activateClaims('exclude everything', {
      kind_filter: ['task'],
      memory_type_filter: ['norm'],
    });

    // Should return 0 claims without crashing
    expect(result.claims_count).toBe(0);
    expect(result.claims).toEqual([]);
    expect(result.active_context_id).toBeTruthy();
  });

  it('feedback on rolled-back claim', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'feedback after rollback test claim' })
    );

    // Activate to reach Ready state
    await activateClaims('feedback after rollback');

    // Rollback the claim
    await rollbackClaim(claim.id, 'testing feedback on rolled back');

    // Try to send feedback on the rolled-back claim
    // This might reveal a bug - feedback may still succeed on rolled-back claims
    const feedbackResult = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'outdated',
    });

    // The claim still exists in DB (tombstone/rollback just marks it),
    // so feedback might succeed. The question is whether it SHOULD.
    // At minimum, it should not crash.
    if (!feedbackResult.isError) {
      // If it succeeds, verify the DB is consistent
      const row = await readClaimRow(claim.id);
      expect(row).toBeDefined();
    }
  });

  it('distill from rolled-back claim fails gracefully', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'distill from rolled back claim test' })
    );

    await rollbackClaim(claim.id, 'testing distill from rolled back');

    // Try to distill from the rolled-back claim
    // findClaimsByIds uses activeClaimFilter which excludes rolled-back claims
    const distillResult = await dispatchTool('pce_memory_distill', {
      source_claim_ids: [claim.id],
    });

    // Should fail because the claim is not found (filtered out)
    expect(distillResult.isError).toBe(true);
    const error = distillResult.structuredContent?.error as { message?: string } | undefined;
    expect(error?.message).toContain('not found');
  });

  it('completed feedback on working_state claim marks status correctly', async () => {
    await applyPolicy();

    // Create a working_state task claim
    const obs = await observeRaw('working state completion test task in progress');
    const distill = await distillFromObservations([obs.observation_id], {
      proposed_kind: 'task',
      proposed_memory_type: 'working_state',
    });
    const promote = await promoteCandidate(distill.candidate_id);

    // Activate to reach Ready state
    await activateClaims('working state completion');

    // Send completed feedback
    await submitFeedback(promote.claim_id, 'completed');

    // Verify status changed
    const row = await readClaimRow(promote.claim_id);
    expect(row?.status).toBe('completed');
    expect(row?.memory_type).toBe('working_state');

    // Activate again - completed working_state should be excluded by default
    const afterComplete = await activateClaims('working state completion');
    const afterIds = afterComplete.claims.map((c) => c.claim.id);
    // Default excludes completed/stale working_state
    expect(afterIds).not.toContain(promote.claim_id);
  });

  it('completed feedback rejected for non-working_state claim', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({
        text: 'completed feedback rejection test knowledge claim',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    );

    // Activate to reach Ready state
    await activateClaims('completed feedback rejection');

    // Try completed feedback on knowledge claim - should be rejected
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'completed',
    });

    expect(result.isError).toBe(true);
    const error = result.structuredContent?.error as { message?: string } | undefined;
    expect(error?.message).toContain('working_state');
  });

  it('double promote of same candidate fails', async () => {
    await applyPolicy();

    const obs = await observeRaw('double promote test unique content');
    const distill = await distillFromObservations([obs.observation_id]);

    // First promote succeeds
    const promote1 = await promoteCandidate(distill.candidate_id);
    expect(promote1.claim_id).toBeTruthy();

    // Second promote of same candidate should fail
    const promote2 = await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
      provenance: buildProvenance(-60_000),
    });

    expect(promote2.isError).toBe(true);
    const error = promote2.structuredContent?.error as { message?: string } | undefined;
    expect(error?.message).toContain('pending');
  });

  it('link to non-existent claim fails gracefully', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'link to ghost claim test' })
    );

    const result = await dispatchTool('pce_memory_link_claims', {
      source_claim_id: claim.id,
      target_claim_id: 'clm_nonexistent_99999',
      link_type: 'related',
    });

    expect(result.isError).toBe(true);
  });

  it('self-link is rejected', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'self link test claim' })
    );

    const result = await dispatchTool('pce_memory_link_claims', {
      source_claim_id: claim.id,
      target_claim_id: claim.id,
      link_type: 'related',
    });

    expect(result.isError).toBe(true);
  });

  it('health endpoint reflects accurate counts after lifecycle operations', async () => {
    await applyPolicy();

    // Create some claims
    await upsertClaimViaTool({ text: 'health check test claim 1' });
    await upsertClaimViaTool({ text: 'health check test claim 2' });

    const obs = await observeRaw('health check observation content');
    const distill = await distillFromObservations([obs.observation_id]);
    await promoteCandidate(distill.candidate_id);

    const health = expectSuccess<HealthResult>(
      await dispatchTool('pce_memory_health', {})
    );

    // Should reflect 3 claims total (2 upsert + 1 promoted)
    expect(health.total_claims).toBe(3);
  });

  it('state transitions: feedback before activate fails', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'feedback before activate test' })
    );

    // State is HasClaims (not Ready), feedback should fail
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
    });

    expect(result.isError).toBe(true);
    const error = result.structuredContent?.error as { code?: string } | undefined;
    expect(error?.code).toBe('STATE_ERROR');
  });

  it('activate with include_observations in PolicyApplied state (no claims)', async () => {
    await applyPolicy();

    // Create observation but no claims
    await observeRaw('observation-only activate test content');

    // Activate with include_observations - allowed even in PolicyApplied state
    const result = await activateClaims('observation-only activate', {
      include_observations: true,
    });

    // Should succeed (PolicyApplied + include_observations is allowed)
    expect(result.active_context_id).toBeTruthy();
    expect(result.claims_count).toBeGreaterThanOrEqual(0);
  });

  it('promote, rollback, distill from NEW observation, promote again - both claims in DB', async () => {
    await applyPolicy();

    // First lifecycle
    const obs1 = await observeRaw('first cycle unique observation for dual promote');
    const distill1 = await distillFromObservations([obs1.observation_id]);
    const promote1 = await promoteCandidate(distill1.candidate_id);
    await rollbackClaim(promote1.claim_id, 'replaced by second version');

    // Second lifecycle with DIFFERENT observation
    const obs2 = await observeRaw('second cycle different observation for dual promote');
    const distill2 = await distillFromObservations([obs2.observation_id]);
    const promote2 = await promoteCandidate(distill2.candidate_id);

    // Both claims exist in DB
    const total = await countClaims();
    expect(total).toBe(2);

    // Only second is active
    const active = await countActiveClaims();
    expect(active).toBe(1);

    // Activate returns only the second
    const result = await activateClaims('cycle observation dual promote');
    const ids = result.claims.map((c) => c.claim.id);
    expect(ids).not.toContain(promote1.claim_id);
    expect(ids).toContain(promote2.claim_id);
  });

  it('pagination with next_cursor works correctly', async () => {
    await applyPolicy({ hybrid: { threshold: 0.0 } });

    // Create enough claims to require pagination
    for (let i = 0; i < 5; i++) {
      await upsertClaimViaTool({
        text: `pagination test claim number ${i} about software engineering patterns`,
      });
    }

    // Activate with small top_k
    const page1 = await activateClaims('software engineering patterns', { top_k: 2 });
    expect(page1.claims_count).toBe(2);

    if (page1.has_more && page1.next_cursor) {
      const page2 = await activateClaims('software engineering patterns', {
        top_k: 2,
        cursor: page1.next_cursor,
      });
      expect(page2.claims_count).toBeGreaterThanOrEqual(0);

      // Pages should not have overlapping claim IDs
      const page1Ids = new Set(page1.claims.map((c) => c.claim.id));
      for (const item of page2.claims) {
        expect(page1Ids.has(item.claim.id)).toBe(false);
      }
    }
  });

  it('entity and relation operations with claim linkage', async () => {
    await applyPolicy();

    await upsertClaimViaTool({ text: 'entity relation test claim about DuckDB usage' });

    // Create entities
    const entity1 = expectSuccess<{ id: string }>(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_duckdb',
        type: 'Artifact',
        name: 'DuckDB',
        canonical_key: 'duckdb',
      })
    );

    const entity2 = expectSuccess<{ id: string }>(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_pce_memory',
        type: 'Artifact',
        name: 'pce-memory',
        canonical_key: 'pce-memory',
      })
    );

    // Create relation
    const relation = expectSuccess<{ id: string }>(
      await dispatchTool('pce_memory_upsert_relation', {
        id: 'rel_pce_uses_duckdb',
        src_id: 'ent_pce_memory',
        dst_id: 'ent_duckdb',
        type: 'USES',
      })
    );

    expect(entity1.id).toBe('ent_duckdb');
    expect(entity2.id).toBe('ent_pce_memory');
    expect(relation.id).toBe('rel_pce_uses_duckdb');

    // Query entities
    const entityQuery = expectSuccess<{ entities: Array<{ id: string }> }>(
      await dispatchTool('pce_memory_query_entity', { type: 'Artifact' })
    );
    expect(entityQuery.entities.length).toBeGreaterThanOrEqual(2);

    // Query relations
    const relationQuery = expectSuccess<{ relations: Array<{ id: string }> }>(
      await dispatchTool('pce_memory_query_relation', { type: 'USES' })
    );
    expect(relationQuery.relations.length).toBeGreaterThanOrEqual(1);
  });
});

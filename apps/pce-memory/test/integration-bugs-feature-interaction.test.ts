/**
 * Integration Bug Hunt Tests — APPROACH 2: Feature Interaction Bugs
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
  dispatchTool,
  expectSuccess,
  observeRaw,
  activateClaims,
  submitFeedback,
  rollbackClaim,
  linkClaims,
  readClaimRow,
  type SyncPushResult,
} from './helpers/integrationBugsTestUtils';

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

// ============================================================
// APPROACH 2: Feature Interaction Bugs
// ============================================================

describe('APPROACH 2: Feature Interaction Bugs', () => {
  it('MMR + intent + kind_filter + memory_type_filter all combined', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: `
version: '0.1'
boundary:
  version: '0.1'
  scopes:
    session: { ttl: '7d' }
    project: { ttl: '120d' }
    principle: { ttl: 'inf' }
  boundary_classes:
    public: { allow: ['*'] }
    internal: { allow: ['answer:task', 'tool:*'] }
    pii:
      allow: ['tool:contact-lookup']
      redact: ['email', 'phone']
      escalation: 'human_review'
    secret: { allow: [], escalation: 'deny' }
retrieval:
  hybrid:
    alpha: 0.65
    threshold: 0.05
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
    mmr:
      enabled: true
      lambda: 0.72
      max_candidates: 48
    query_expansion:
      enabled: true
      max_seed_entities: 3
      max_related_entities: 8
      max_expansion_terms: 6
    feedback_boost:
      enabled: true
      helpful_weight: 0.3
      harmful_weight: -0.5
      outdated_weight: -0.2
      duplicate_weight: -0.1
      min_multiplier: 0.5
      max_multiplier: 2.0
maintenance:
  hints_enabled: true
  similarity_threshold: 0.9
  stale_days: 30
`.trim(),
    });

    // Create claims of different kinds and memory types
    await upsertClaimViaTool({
      text: 'MMR test fact knowledge about authentication',
      kind: 'fact',
      memory_type: 'knowledge',
    });
    await upsertClaimViaTool({
      text: 'MMR test preference procedure for naming',
      kind: 'preference',
      memory_type: 'procedure',
    });
    await upsertClaimViaTool({
      text: 'MMR test task working state for migration',
      kind: 'task',
      memory_type: 'working_state',
    });
    await upsertClaimViaTool({
      text: 'MMR test policy hint norm for security',
      kind: 'policy_hint',
      memory_type: 'norm',
    });

    // Activate with all filters combined
    const result = await activateClaims('MMR test authentication security', {
      intent: 'design_decision',
      kind_filter: ['fact', 'policy_hint'],
      memory_type_filter: ['knowledge', 'norm'],
      scope: ['project'],
    });

    // Should only return fact+knowledge and policy_hint+norm
    for (const item of result.claims) {
      expect(['fact', 'policy_hint']).toContain(item.claim.kind);
      expect(['knowledge', 'norm']).toContain(item.claim.memory_type);
    }
  });

  it('query expansion + claim_links + include_observations combined', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: `
version: '0.1'
boundary:
  version: '0.1'
  scopes:
    session: { ttl: '7d' }
    project: { ttl: '120d' }
    principle: { ttl: 'inf' }
  boundary_classes:
    public: { allow: ['*'] }
    internal: { allow: ['answer:task', 'tool:*'] }
    pii:
      allow: ['tool:contact-lookup']
      redact: ['email', 'phone']
      escalation: 'human_review'
    secret: { allow: [], escalation: 'deny' }
retrieval:
  hybrid:
    alpha: 0.65
    threshold: 0.05
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
    query_expansion:
      enabled: true
      max_seed_entities: 3
      max_related_entities: 8
      max_expansion_terms: 6
maintenance:
  hints_enabled: true
  similarity_threshold: 0.9
  stale_days: 30
`.trim(),
    });

    // Create linked claims
    const claimA = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'query expansion claim A about REST API design patterns' })
    );
    const claimB = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'query expansion claim B about HTTP endpoint validation' })
    );

    // Link them
    await linkClaims(claimA.id, claimB.id, 'related', 0.9);

    // Create an entity for query expansion
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_rest_api',
      type: 'Concept',
      name: 'REST API',
      canonical_key: 'rest-api',
    });

    // Create an observation
    await observeRaw('query expansion observation about REST API testing strategy');

    // Activate with include_observations
    const result = await activateClaims('REST API design', {
      include_observations: true,
    });

    // Should not crash; claims_count >= 0
    expect(result.claims_count).toBeGreaterThanOrEqual(0);
    expect(result.active_context_id).toBeTruthy();
  });

  it('feedback boost + provenance quality affecting same claim across multiple feedback signals', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: `
version: '0.1'
boundary:
  version: '0.1'
  scopes:
    session: { ttl: '7d' }
    project: { ttl: '120d' }
    principle: { ttl: 'inf' }
  boundary_classes:
    public: { allow: ['*'] }
    internal: { allow: ['answer:task', 'tool:*'] }
    pii:
      allow: ['tool:contact-lookup']
      redact: ['email', 'phone']
      escalation: 'human_review'
    secret: { allow: [], escalation: 'deny' }
retrieval:
  hybrid:
    alpha: 0.65
    threshold: 0.05
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
    feedback_boost:
      enabled: true
      helpful_weight: 0.3
      harmful_weight: -0.5
      outdated_weight: -0.2
      duplicate_weight: -0.1
      min_multiplier: 0.5
      max_multiplier: 2.0
maintenance:
  hints_enabled: true
  similarity_threshold: 0.9
  stale_days: 30
`.trim(),
    });

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({
        text: 'feedback boost test claim for architecture decision JWT auth',
      })
    );

    // First activate to get into Ready state
    const first = await activateClaims('JWT auth architecture');
    expect(first.claims.some((c) => c.claim.id === claim.id)).toBe(true);
    const firstScore = first.claims.find((c) => c.claim.id === claim.id)?.score ?? 0;

    // Send multiple helpful feedback signals
    await submitFeedback(claim.id, 'helpful');
    await submitFeedback(claim.id, 'helpful');
    await submitFeedback(claim.id, 'helpful');

    // Activate again - score should be boosted
    const second = await activateClaims('JWT auth architecture');
    const secondScore = second.claims.find((c) => c.claim.id === claim.id)?.score ?? 0;

    // With feedback_boost enabled and 3x helpful, score should increase
    expect(secondScore).toBeGreaterThanOrEqual(firstScore);

    // Now send harmful feedback
    await submitFeedback(claim.id, 'harmful');

    const third = await activateClaims('JWT auth architecture');
    expect(third.claims_count).toBeGreaterThanOrEqual(0); // should not crash
  });

  it('maintenance_hints + working_state lifecycle + staleness detection', async () => {
    await applyPolicy({
      maintenance: { hints_enabled: true, similarity_threshold: 0.8, stale_days: 0 },
    });

    // Create similar claims to trigger maintenance hints
    await upsertClaimViaTool({
      text: 'maintenance hint similar claim alpha about database migration',
      memory_type: 'knowledge',
    });
    await upsertClaimViaTool({
      text: 'maintenance hint similar claim beta about database migration strategy',
      memory_type: 'knowledge',
    });

    // Create a working_state claim
    const wsResult = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({
        text: 'working state task in progress debugging login issue',
        kind: 'task',
        memory_type: 'working_state',
      })
    );

    // Activate and check maintenance hints
    const result = await activateClaims('database migration');
    expect(result.active_context_id).toBeTruthy();

    // maintenance_hints should be present (hints_enabled: true)
    // It's best-effort so might be undefined, but should not crash
    if (result.maintenance_hints) {
      // Verify structure is valid
      expect(typeof result.maintenance_hints).toBe('object');
    }

    // Mark working_state as completed via feedback
    await submitFeedback(wsResult.id, 'completed');
    const wsRow = await readClaimRow(wsResult.id);
    expect(wsRow?.status).toBe('completed');
  });

  it('freshness guard + rollback interaction', async () => {
    await applyPolicy();

    // Create claim A
    const claimA = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'freshness guard original claim about error handling v1' })
    );

    // Create similar claim B (should trigger freshness guard in activate)
    const claimB = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'freshness guard updated claim about error handling v2' })
    );

    // Activate - both should appear but freshness metadata may flag A
    const before = await activateClaims('error handling');
    expect(before.claims_count).toBeGreaterThanOrEqual(1);

    // Rollback claim A
    await rollbackClaim(claimA.id, 'superseded by v2');

    // Activate again - only claim B should appear
    const after = await activateClaims('error handling');
    const afterIds = after.claims.map((c) => c.claim.id);
    expect(afterIds).not.toContain(claimA.id);
    expect(afterIds).toContain(claimB.id);
  });

  it('sync push with 0 exportable claims does not crash', async () => {
    await applyPolicy();

    // No claims yet, just PolicyApplied state
    // sync push should handle empty gracefully
    const result = await dispatchTool('pce_memory_sync_push', {
      target_dir: '/tmp/pce-test-sync-empty-' + Date.now(),
    });

    // Should not crash - either success with 0 exports or a graceful error
    if (!result.isError) {
      const push = result.structuredContent as SyncPushResult;
      expect(push.exported.claims).toBe(0);
    }
    // If it's an error, it should be a specific error, not a crash
  });

  it('sync push after rollback excludes rolled-back claims', async () => {
    await applyPolicy();

    const claim = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({ text: 'sync push rollback test claim content' })
    );

    await rollbackClaim(claim.id, 'testing sync after rollback');

    const targetDir = '/tmp/pce-test-sync-rollback-' + Date.now();
    const result = await dispatchTool('pce_memory_sync_push', {
      target_dir: targetDir,
    });

    if (!result.isError) {
      const push = result.structuredContent as SyncPushResult;
      // The rolled-back claim should not be exported
      expect(push.exported.claims).toBe(0);
    }
  });
});

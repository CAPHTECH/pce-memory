/**
 * Integration Bug Hunt Tests
 *
 * APPROACH 1: Full Lifecycle Stress (10 sequential cycles)
 * APPROACH 2: Feature Interaction Bugs (MMR, filters, feedback boost, maintenance hints, sync)
 * APPROACH 3: Edge Case Workflows (rollback-redistill, freshness guard, circular links, etc.)
 */
import { beforeEach, describe, expect, it } from 'vitest';
import { getConnection } from '../src/db/connection';
import {
  applyPolicy,
  dispatchTool,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

type ToolResponse = Awaited<ReturnType<typeof dispatchTool>>;
type ToolStructuredContent = NonNullable<ToolResponse['structuredContent']>;

type ObserveResult = {
  observation_id: string;
  effective_boundary_class?: string;
};

type DistillResult = {
  candidate_id: string;
  distilled_text: string;
  proposed_kind: string;
  proposed_scope: string;
  proposed_memory_type: string | null;
  proposed_boundary_class: string;
  status: string;
};

type PromoteResult = {
  claim_id: string;
  is_new: boolean;
  promoted_from: string;
  rollback_token: string;
};

type RollbackResult = {
  rollback_id: string;
  superseded_claim_id: string;
};

type ActivateResult = {
  active_context_id: string;
  intent?: string;
  claims_count: number;
  claims: Array<{
    claim: {
      id: string;
      scope: string;
      boundary_class: string;
      kind: string;
      memory_type?: string | null;
      text?: string;
    };
    score: number;
    score_breakdown?: Record<string, unknown>;
    selection_reason?: string;
  }>;
  maintenance_hints?: {
    stale_claims?: Array<{ id: string }>;
    similar_pairs?: Array<{ claim_a_id: string; claim_b_id: string }>;
  };
  next_cursor?: string;
  has_more?: boolean;
};

type FeedbackResult = {
  id: string;
  claim_id: string;
  signal: string;
};

type LinkResult = {
  id: string;
  is_new: boolean;
  source_claim_id: string;
  target_claim_id: string;
  link_type: string;
  confidence: number;
};

type SyncPushResult = {
  exported: { claims: number; entities?: number; relations?: number };
  target_dir: string;
  manifest_updated: boolean;
};

type HealthResult = {
  total_claims: number;
  by_kind: Record<string, number>;
  by_scope: Record<string, number>;
};

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

function expectSuccess<T extends ToolStructuredContent>(result: ToolResponse): T {
  if (result.isError) {
    const errorText = result.content?.[0]?.text ?? 'unknown error';
    const errorDetail = result.structuredContent?.error ?? {};
    throw new Error(`Expected success but got error: ${errorText} ${JSON.stringify(errorDetail)}`);
  }
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent as T;
}

function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

function buildProvenance(
  offsetMs: number,
  note?: string
): { at: string; actor: string; note?: string } {
  return note
    ? { at: isoOffset(offsetMs), actor: 'claude', note }
    : { at: isoOffset(offsetMs), actor: 'claude' };
}

async function observeRaw(
  content: string,
  extra: Record<string, unknown> = {}
): Promise<ObserveResult> {
  return expectSuccess<ObserveResult>(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      extract: { mode: 'noop' },
      ...extra,
    })
  );
}

async function distillFromObservations(
  observationIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: observationIds,
      ...extra,
    })
  );
}

async function distillFromClaims(
  claimIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_claim_ids: claimIds,
      ...extra,
    })
  );
}

async function promoteCandidate(
  candidateId: string,
  extra: Record<string, unknown> = {}
): Promise<PromoteResult> {
  return expectSuccess<PromoteResult>(
    await dispatchTool('pce_memory_promote', {
      candidate_id: candidateId,
      provenance: buildProvenance(-60_000),
      ...extra,
    })
  );
}

async function rollbackClaim(claimId: string, reason: string): Promise<RollbackResult> {
  return expectSuccess<RollbackResult>(
    await dispatchTool('pce_memory_rollback', {
      claim_id: claimId,
      reason,
      provenance: buildProvenance(-30_000, reason),
    })
  );
}

async function activateClaims(
  q: string,
  overrides: Record<string, unknown> = {}
): Promise<ActivateResult> {
  return expectSuccess<ActivateResult>(
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 10,
      q,
      ...overrides,
    })
  );
}

async function submitFeedback(
  claimId: string,
  signal: string
): Promise<FeedbackResult> {
  return expectSuccess<FeedbackResult>(
    await dispatchTool('pce_memory_feedback', {
      claim_id: claimId,
      signal,
    })
  );
}

async function linkClaims(
  sourceClaimId: string,
  targetClaimId: string,
  linkType: string,
  confidence?: number
): Promise<LinkResult> {
  return expectSuccess<LinkResult>(
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: sourceClaimId,
      target_claim_id: targetClaimId,
      link_type: linkType,
      ...(confidence !== undefined ? { confidence } : {}),
    })
  );
}

async function readClaimRow(claimId: string): Promise<
  | {
      scope: string;
      boundary_class: string;
      utility: number;
      confidence: number;
      tombstone: boolean;
      status: string;
      memory_type: string | null;
    }
  | undefined
> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT scope, boundary_class, utility, confidence, COALESCE(tombstone, FALSE) as tombstone, status, memory_type FROM claims WHERE id = $1',
    [claimId]
  );
  const rows = reader.getRowObjects() as Array<{
    scope: string;
    boundary_class: string;
    utility: number;
    confidence: number;
    tombstone: boolean;
    status: string;
    memory_type: string | null;
  }>;
  return rows[0];
}

async function countClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM claims');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

async function countActiveClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT COUNT(*) as cnt FROM claims c
     WHERE COALESCE(c.tombstone, FALSE) = FALSE
     AND NOT EXISTS (
       SELECT 1 FROM promotion_queue pq
       WHERE pq.accepted_claim_id = c.id AND pq.status = 'rolled_back'
     )`
  );
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

async function countObservations(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM observations');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

async function countPromotionQueue(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM promotion_queue');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

async function countFeedback(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM feedback');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

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
      expect(obs.observation_id).toBeTruthy();

      // distill
      const distill = await distillFromObservations([obs.observation_id]);
      expect(distill.candidate_id).toBeTruthy();
      expect(distill.status).toBe('pending');

      // promote
      const promote = await promoteCandidate(distill.candidate_id);
      expect(promote.claim_id).toBeTruthy();
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
    await upsertClaimViaTool({ text: 'MMR test fact knowledge about authentication', kind: 'fact', memory_type: 'knowledge' });
    await upsertClaimViaTool({ text: 'MMR test preference procedure for naming', kind: 'preference', memory_type: 'procedure' });
    await upsertClaimViaTool({ text: 'MMR test task working state for migration', kind: 'task', memory_type: 'working_state' });
    await upsertClaimViaTool({ text: 'MMR test policy hint norm for security', kind: 'policy_hint', memory_type: 'norm' });

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
      await upsertClaimViaTool({ text: 'feedback boost test claim for architecture decision JWT auth' })
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

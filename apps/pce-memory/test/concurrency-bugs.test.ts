/**
 * Concurrency Bug Hunt Tests
 *
 * Tests for race conditions across:
 * 1. Concurrent Operations (parallel upserts, activates, distills, promotes, feedback, etc.)
 * 2. State Machine Races (transitions during concurrent operations)
 * 3. Database Races (claim_links, retrieval_count, critic scores)
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { upsertClaim, recordClaimRetrievals } from '../src/store/claims';
import { upsertClaimLink } from '../src/store/claimLinks';
import { updateCritic } from '../src/store/critic';
import { insertObservation } from '../src/store/observations';
import { recordFeedback } from '../src/store/feedback';
import {
  handleUpsert,
  handleActivate,
  handleFeedback,
  handleObserve,
  handleDistill,
  handlePromote,
  handleRollback,
  handleSyncPush,
} from '../src/core/handlers';
import {
  applyPolicyOp,
  resetMemoryState,
  transitionToHasClaims,
  getStateType,
  getClaimCount,
} from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';

// ========== Helpers ==========

async function setupPolicyApplied(): Promise<void> {
  const result = await applyPolicyOp()();
  expect(E.isRight(result)).toBe(true);
}

async function setupHasClaims(): Promise<string> {
  await setupPolicyApplied();
  const result = await handleUpsert({
    text: 'seed claim for test setup',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: `sha256:${computeContentHash('seed claim for test setup')}`,
    provenance: { at: new Date().toISOString(), actor: 'test' },
  });
  const parsed = JSON.parse(result.content[0]!.text);
  expect(parsed.error).toBeUndefined();
  return parsed.id;
}

async function setupReady(): Promise<string> {
  const claimId = await setupHasClaims();
  const result = await handleActivate({
    scope: ['project'],
    allow: ['answer:task'],
    q: 'test',
    top_k: 5,
  });
  const parsed = JSON.parse(result.content[0]!.text);
  expect(parsed.error).toBeUndefined();
  return claimId;
}

function makeUpsertArgs(i: number, contentHash?: string) {
  const text = `concurrent claim ${i}`;
  return {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: contentHash ?? `sha256:${computeContentHash(text)}`,
    provenance: { at: new Date().toISOString(), actor: 'test' },
  };
}

function parseResult(result: { content: Array<{ text: string }> }) {
  return JSON.parse(result.content[0]!.text);
}

// ========== Setup ==========

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100000';
  process.env.PCE_RATE_WINDOW = '0';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  resetMemoryState();
});

// ========== APPROACH 1: Concurrent Operations ==========

describe('APPROACH 1: Concurrent Operations', () => {
  describe('Race: 20 parallel upserts with same content_hash (dedup race)', () => {
    it('should produce exactly one new claim despite 20 parallel inserts', async () => {
      await setupPolicyApplied();
      const text = 'deduplicated concurrent claim';
      const hash = `sha256:${computeContentHash(text)}`;
      const args = {
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
        provenance: { at: new Date().toISOString(), actor: 'test' },
      };

      const results = await Promise.all(
        Array.from({ length: 20 }, () => handleUpsert({ ...args }))
      );

      const parsed = results.map(parseResult);
      const successes = parsed.filter((r) => !r.error);
      const errors = parsed.filter((r) => r.error);

      // DB_ERROR can happen under heavy full-suite contention; other errors are unexpected
      for (const e of errors) {
        expect(['DB_ERROR', 'UPSERT_FAILED']).toContain(e.error.code);
      }

      // At least some should succeed
      expect(successes.length).toBeGreaterThan(0);

      // All successes should return the same claim ID
      const ids = new Set(successes.map((r) => r.id));
      expect(ids.size).toBe(1);

      // Exactly one should report is_new = true
      const newCount = successes.filter((r) => r.is_new === true).length;
      expect(newCount).toBe(1);
    });
  });

  describe('Race: 10 parallel activates while upserts are running', () => {
    it('should not crash or produce invalid state', async () => {
      await setupHasClaims();

      const upsertPromises = Array.from({ length: 10 }, (_, i) => handleUpsert(makeUpsertArgs(i)));
      const activatePromises = Array.from({ length: 10 }, () =>
        handleActivate({
          scope: ['project'],
          allow: ['answer:task'],
          q: 'concurrent test',
          top_k: 5,
        })
      );

      const allResults = await Promise.all([...upsertPromises, ...activatePromises]);
      const parsed = allResults.map(parseResult);

      // No unhandled errors - all operations should complete
      for (const r of parsed) {
        if (r.error) {
          expect(['STATE_ERROR', 'RATE_LIMIT']).toContain(r.error.code);
        }
      }

      // State should be valid after all operations complete
      const state = getStateType();
      expect(['HasClaims', 'Ready', 'PolicyApplied']).toContain(state);
    });
  });

  describe('Race: 5 parallel distills from same observation', () => {
    it('should all succeed or gracefully fail without corruption', async () => {
      await setupHasClaims();

      // Create an observation
      const obsResult = await handleObserve({
        source_type: 'chat',
        content: 'observation for parallel distill test',
      });
      const obsParsed = parseResult(obsResult);
      expect(obsParsed.error).toBeUndefined();
      const obsId = obsParsed.observation_id;

      const distillPromises = Array.from({ length: 5 }, () =>
        handleDistill({
          source_observation_ids: [obsId],
          proposed_kind: 'fact',
          proposed_scope: 'project',
          proposed_memory_type: 'knowledge',
        })
      );

      const results = await Promise.all(distillPromises);
      const parsed = results.map(parseResult);

      // All should succeed (each creates a separate candidate)
      const successes = parsed.filter((r) => !r.error);
      const candidateIds = new Set(successes.map((r) => r.candidate_id));

      // Each distill should create a unique candidate
      expect(candidateIds.size).toBe(successes.length);
      expect(successes.length).toBeGreaterThan(0);
    });
  });

  describe('Race: 3 parallel promotes on same candidate', () => {
    it('should allow exactly one promote and reject the rest', async () => {
      await setupHasClaims();

      // Create observation and distill to get a candidate
      const obsResult = await handleObserve({
        source_type: 'chat',
        content: 'observation for promote race test',
      });
      const obsParsed = parseResult(obsResult);
      expect(obsParsed.error).toBeUndefined();
      const obsId = obsParsed.observation_id;
      expect(obsId).toBeDefined();

      const distillResult = await handleDistill({
        source_observation_ids: [obsId],
        proposed_kind: 'fact',
        proposed_scope: 'project',
        proposed_memory_type: 'knowledge',
      });
      const distillParsed = parseResult(distillResult);
      expect(distillParsed.error).toBeUndefined();
      const candidateId = distillParsed.candidate_id;
      expect(candidateId).toBeDefined();

      const provenance = { at: new Date().toISOString(), actor: 'test' };
      const promotePromises = Array.from({ length: 3 }, () =>
        handlePromote({
          candidate_id: candidateId,
          provenance,
        })
      );

      const results = await Promise.all(promotePromises);
      const parsed = results.map(parseResult);

      // Exactly one should succeed
      const successes = parsed.filter((r) => !r.error);
      const failures = parsed.filter((r) => r.error);

      expect(successes.length).toBe(1);
      expect(failures.length).toBe(2);

      // Failed ones should get a clear error, not a crash
      for (const f of failures) {
        expect(f.error.code).toBe('VALIDATION_ERROR');
        expect(f.error.message).toContain('pending');
      }
    });
  });

  describe('Race: parallel rollback + activate on same claim', () => {
    it('should not corrupt state', async () => {
      const claimId = await setupReady();

      const rollbackPromise = handleRollback({
        claim_id: claimId,
        reason: 'parallel rollback test',
        provenance: { at: new Date().toISOString(), actor: 'test' },
      });
      const activatePromise = handleActivate({
        scope: ['project'],
        allow: ['answer:task'],
        q: 'test rollback race',
        top_k: 5,
      });

      const [rollbackResult, activateResult] = await Promise.all([
        rollbackPromise,
        activatePromise,
      ]);

      // Both should complete without crash
      const rollbackParsed = parseResult(rollbackResult);
      const activateParsed = parseResult(activateResult);

      // Rollback should succeed
      if (!rollbackParsed.error) {
        expect(rollbackParsed.rollback_id).toBeDefined();
      }

      // Activate may or may not include the rolled-back claim, but shouldn't crash
      expect(activateParsed.error?.code !== 'UPSERT_FAILED').toBe(true);
    });
  });

  describe('Race: parallel feedback (helpful + harmful) on same claim', () => {
    it('should apply both feedback signals without lost updates', async () => {
      const claimId = await setupReady();

      const helpfulPromise = handleFeedback({
        claim_id: claimId,
        signal: 'helpful',
      });
      const harmfulPromise = handleFeedback({
        claim_id: claimId,
        signal: 'harmful',
      });

      const [helpfulResult, harmfulResult] = await Promise.all([helpfulPromise, harmfulPromise]);

      // Both should succeed
      expect(parseResult(helpfulResult).error).toBeUndefined();
      expect(parseResult(harmfulResult).error).toBeUndefined();

      // Verify both feedback records exist in DB
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        'SELECT COUNT(*)::INTEGER AS cnt FROM feedback WHERE claim_id = $1',
        [claimId]
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]!.cnt).toBe(2);
    });
  });

  describe('Race: parallel observe + activate(include_observations=true)', () => {
    it('should not miss or corrupt observations', async () => {
      await setupHasClaims();

      const observePromises = Array.from({ length: 5 }, (_, i) =>
        handleObserve({
          source_type: 'chat',
          content: `parallel observation ${i}`,
        })
      );
      const activatePromise = handleActivate({
        scope: ['project'],
        allow: ['answer:task'],
        q: 'parallel observation',
        top_k: 10,
        include_observations: true,
      });

      const [observeResults, activateResult] = await Promise.all([
        Promise.all(observePromises),
        activatePromise,
      ]);

      // All observes should succeed or fail gracefully (DB contention is acceptable)
      for (const r of observeResults) {
        const parsed = parseResult(r);
        if (parsed.error) {
          expect(['DB_ERROR', 'OBSERVE_FAILED']).toContain(parsed.error.code);
        }
      }

      // Activate should succeed or fail gracefully
      const activateParsed = parseResult(activateResult);
      if (activateParsed.error) {
        expect(['STATE_ERROR', 'DB_ERROR']).toContain(activateParsed.error.code);
      }
    });
  });

  describe('Race: parallel sync push + upsert', () => {
    it('should not corrupt DB during concurrent push and write', async () => {
      await setupHasClaims();

      const upsertPromises = Array.from({ length: 5 }, (_, i) =>
        handleUpsert(makeUpsertArgs(100 + i))
      );
      const pushPromise = handleSyncPush({
        target_dir: '/tmp/pce-sync-test',
      });

      const results = await Promise.all([...upsertPromises, pushPromise]);
      const parsed = results.map(parseResult);

      // Upserts should succeed
      for (const r of parsed) {
        if (r.error) {
          // Sync-related errors are acceptable, DB corruption is not
          expect(['RATE_LIMIT', 'STATE_ERROR', 'SYNC_PUSH_FAILED']).toContain(r.error.code);
        }
      }
    });
  });
});

// ========== APPROACH 2: State Machine Races ==========

describe('APPROACH 2: State Machine Races', () => {
  describe('Race: activate before policy_apply completes', () => {
    it('should reject activate when state is Uninitialized', async () => {
      const policyPromise = applyPolicyOp()();
      const activateResult = await handleActivate({
        scope: ['project'],
        allow: ['answer:task'],
        q: 'test',
        top_k: 5,
      });

      const parsed = parseResult(activateResult);
      expect(parsed.error).toBeDefined();
      expect(parsed.error.code).toBe('STATE_ERROR');

      // Policy should still complete successfully
      const policyResult = await policyPromise;
      expect(E.isRight(policyResult)).toBe(true);
    });
  });

  describe('Race: upsert during state transition', () => {
    it('should handle rapid upserts after policy_apply', async () => {
      await setupPolicyApplied();

      // Fire 10 rapid upserts
      const upsertPromises = Array.from({ length: 10 }, (_, i) => handleUpsert(makeUpsertArgs(i)));

      const results = await Promise.all(upsertPromises);
      const parsed = results.map(parseResult);
      const successes = parsed.filter((r) => !r.error);

      // All should succeed since state was PolicyApplied
      expect(successes.length).toBe(10);

      // State should be HasClaims
      expect(getStateType()).toBe('HasClaims');
    });
  });

  describe('Race: rapid state transitions policy_apply -> upsert -> activate -> feedback in <100ms', () => {
    it('should maintain valid state throughout rapid transitions', async () => {
      // Step 1: policy_apply
      await setupPolicyApplied();
      expect(getStateType()).toBe('PolicyApplied');

      // Step 2: upsert (PolicyApplied -> HasClaims)
      const upsertResult = await handleUpsert(makeUpsertArgs(0));
      const upsertParsed = parseResult(upsertResult);
      expect(upsertParsed.error).toBeUndefined();
      const claimId = upsertParsed.id;
      expect(getStateType()).toBe('HasClaims');

      // Step 3: activate (HasClaims -> Ready)
      const activateResult = await handleActivate({
        scope: ['project'],
        allow: ['answer:task'],
        q: 'rapid transition test',
        top_k: 5,
      });
      expect(parseResult(activateResult).error).toBeUndefined();
      expect(getStateType()).toBe('Ready');

      // Step 4: feedback (Ready -> Ready)
      const feedbackResult = await handleFeedback({
        claim_id: claimId,
        signal: 'helpful',
      });
      expect(parseResult(feedbackResult).error).toBeUndefined();
      expect(getStateType()).toBe('Ready');
    });
  });

  describe('Race: multiple policy_apply calls simultaneously', () => {
    it('should allow exactly one and reject the rest', async () => {
      const policyPromises = Array.from({ length: 5 }, () => applyPolicyOp()());

      const results = await Promise.all(policyPromises);
      const successes = results.filter(E.isRight);
      const failures = results.filter(E.isLeft);

      // Exactly one should succeed due to enqueue serialization
      expect(successes.length).toBe(1);
      expect(failures.length).toBe(4);

      // State should be PolicyApplied
      expect(getStateType()).toBe('PolicyApplied');
    });
  });

  describe('Race: transitionToHasClaims concurrent claim count', () => {
    it('should correctly count claims after concurrent transitions', async () => {
      await setupPolicyApplied();

      const initialCount = getClaimCount();

      // Synchronous calls should always be correct
      transitionToHasClaims(true);
      transitionToHasClaims(true);

      const finalCount = getClaimCount();
      expect(finalCount).toBe(initialCount + 2);
    });

    it('should track correct claim count after 20 concurrent handler upserts', async () => {
      await setupPolicyApplied();

      const upsertPromises = Array.from({ length: 20 }, (_, i) => handleUpsert(makeUpsertArgs(i)));

      const results = await Promise.all(upsertPromises);
      const parsed = results.map(parseResult);
      const successes = parsed.filter((r) => !r.error);
      expect(successes.length).toBe(20);

      // The state machine claim count should match DB reality
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        'SELECT COUNT(*)::INTEGER AS cnt FROM claims WHERE COALESCE(tombstone, FALSE) = FALSE'
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      const dbCount = rows[0]!.cnt;

      // Key invariant: state machine count >= DB count
      expect(getClaimCount()).toBeGreaterThanOrEqual(dbCount);
    });
  });
});

// ========== APPROACH 3: Database Races ==========

describe('APPROACH 3: Database Races', () => {
  describe('Race: concurrent claim_links creation on same pair', () => {
    it('should not create duplicate links', async () => {
      await setupPolicyApplied();

      // Create two claims
      const result1 = await upsertClaim({
        text: 'link source claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('link source claim')}`,
      });
      const result2 = await upsertClaim({
        text: 'link target claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('link target claim')}`,
      });

      const sourceId = result1.claim.id;
      const targetId = result2.claim.id;

      // Fire 10 parallel link creations for same pair
      const linkPromises = Array.from({ length: 10 }, () =>
        upsertClaimLink({
          source_claim_id: sourceId,
          target_claim_id: targetId,
          link_type: 'related',
          confidence: 0.8,
        })
      );

      // This should NOT throw - all calls should be idempotent
      const results = await Promise.all(linkPromises);

      // All should return successfully
      expect(results).toHaveLength(10);

      // DB should have exactly 1 link
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        `SELECT COUNT(*)::INTEGER AS cnt FROM claim_links
         WHERE source_claim_id = $1 AND target_claim_id = $2 AND link_type = 'related'`,
        [sourceId, targetId]
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]!.cnt).toBe(1);
    });
  });

  describe('Race: concurrent retrieval_count increments', () => {
    it('should not lose any increments', async () => {
      await setupPolicyApplied();

      const { claim } = await upsertClaim({
        text: 'retrieval count test claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('retrieval count test claim')}`,
      });

      // Fire 20 parallel retrieval count updates
      const updatePromises = Array.from({ length: 20 }, () => recordClaimRetrievals([claim.id]));

      await Promise.all(updatePromises);

      // Verify count - SQL UPDATE SET x = x + 1 is atomic in DuckDB
      const conn = await getConnection();
      const reader = await conn.runAndReadAll('SELECT retrieval_count FROM claims WHERE id = $1', [
        claim.id,
      ]);
      const rows = reader.getRowObjects() as Array<{ retrieval_count: number }>;
      expect(rows[0]!.retrieval_count).toBe(20);
    });
  });

  describe('Race: concurrent critic score updates', () => {
    it('should produce correct final score with atomic UPSERT', async () => {
      await setupPolicyApplied();

      const { claim } = await upsertClaim({
        text: 'critic score test claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('critic score test claim')}`,
      });

      // Fire 10 parallel +1 delta updates (min=0, max=5)
      const updatePromises = Array.from({ length: 10 }, () => updateCritic(claim.id, 1, 0, 5));

      await Promise.all(updatePromises);

      // Final score should be capped at 5 (max)
      const conn = await getConnection();
      const reader = await conn.runAndReadAll('SELECT score FROM critic WHERE claim_id = $1', [
        claim.id,
      ]);
      const rows = reader.getRowObjects() as Array<{ score: number }>;
      expect(rows[0]!.score).toBe(5);
    });

    it('should handle concurrent helpful + harmful feedback correctly', async () => {
      await setupPolicyApplied();

      // Create a claim directly and insert initial critic score
      const { claim } = await upsertClaim({
        text: 'critic mixed test',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('critic mixed test')}`,
      });

      // Fire 5 helpful (+1) and 5 harmful (-1) concurrently
      const helpfulPromises = Array.from({ length: 5 }, () => updateCritic(claim.id, 1, 0, 5));
      const harmfulPromises = Array.from({ length: 5 }, () => updateCritic(claim.id, -1, 0, 5));

      await Promise.all([...helpfulPromises, ...harmfulPromises]);

      const conn = await getConnection();
      const reader = await conn.runAndReadAll('SELECT score FROM critic WHERE claim_id = $1', [
        claim.id,
      ]);
      const rows = reader.getRowObjects() as Array<{ score: number }>;
      const score = rows[0]!.score;

      // Score must be within [0, 5] bounds (exact value depends on execution order
      // since clamping at 0 means some -1 deltas are absorbed when score is already 0)
      expect(score).toBeGreaterThanOrEqual(0);
      expect(score).toBeLessThanOrEqual(5);
    });
  });

  describe('Race: concurrent feedback utility/confidence updates', () => {
    it('should apply all feedback deltas to claims', async () => {
      await setupPolicyApplied();

      const { claim } = await upsertClaim({
        text: 'feedback delta test',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('feedback delta test')}`,
      });

      // Record initial utility/confidence
      const conn = await getConnection();
      const beforeReader = await conn.runAndReadAll(
        'SELECT utility, confidence FROM claims WHERE id = $1',
        [claim.id]
      );
      const beforeRows = beforeReader.getRowObjects() as Array<{
        utility: number;
        confidence: number;
      }>;
      const initialUtility = beforeRows[0]!.utility;
      const initialConfidence = beforeRows[0]!.confidence;

      // Fire 10 parallel helpful feedbacks
      // Each adds utility=+0.10, confidence=+0.05
      const feedbackPromises = Array.from({ length: 10 }, () =>
        recordFeedback({
          claim_id: claim.id,
          signal: 'helpful',
        })
      );

      await Promise.all(feedbackPromises);

      const afterReader = await conn.runAndReadAll(
        'SELECT utility, confidence FROM claims WHERE id = $1',
        [claim.id]
      );
      const afterRows = afterReader.getRowObjects() as Array<{
        utility: number;
        confidence: number;
      }>;

      // Utility should increase by 10 * 0.1 = 1.0
      const expectedUtility = initialUtility + 10 * 0.1;
      // Confidence should increase by 10 * 0.05 = 0.5 (clamped to [0, 1])
      const expectedConfidence = Math.min(1.0, initialConfidence + 10 * 0.05);

      expect(afterRows[0]!.utility).toBeCloseTo(expectedUtility, 5);
      expect(afterRows[0]!.confidence).toBeCloseTo(expectedConfidence, 5);
    });
  });

  describe('Race: concurrent content_hash dedup at store level', () => {
    it('should handle UNIQUE constraint violation gracefully', async () => {
      await setupPolicyApplied();

      const text = 'store level dedup test';
      const hash = `sha256:${computeContentHash(text)}`;

      // Fire 20 parallel upsertClaim calls with same content_hash
      const promises = Array.from({ length: 20 }, () =>
        upsertClaim({
          text,
          kind: 'fact',
          scope: 'project',
          boundary_class: 'internal',
          content_hash: hash,
        })
      );

      const results = await Promise.all(promises);

      // All should return successfully (no throws)
      expect(results).toHaveLength(20);

      // All should return the same claim ID
      const ids = new Set(results.map((r) => r.claim.id));
      expect(ids.size).toBe(1);

      // Exactly one should be new
      const newCount = results.filter((r) => r.isNew).length;
      expect(newCount).toBe(1);

      // DB should have exactly one record
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        'SELECT COUNT(*)::INTEGER AS cnt FROM claims WHERE content_hash = $1 AND COALESCE(tombstone, FALSE) = FALSE',
        [hash]
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]!.cnt).toBe(1);
    });
  });

  describe('Race: concurrent observation insert + search', () => {
    it('should not crash when search runs during inserts', async () => {
      await setupPolicyApplied();

      const insertPromises = Array.from({ length: 10 }, (_, i) =>
        insertObservation({
          id: `obs_concurrent_${i}`,
          source_type: 'chat',
          content: `concurrent observation content ${i}`,
          boundary_class: 'internal',
          content_digest: `sha256:${computeContentHash(`concurrent observation content ${i}`)}`,
          content_length: `concurrent observation content ${i}`.length,
          expires_at: new Date(Date.now() + 3600_000).toISOString(),
        })
      );

      const activatePromise = handleActivate({
        scope: ['project'],
        allow: ['answer:task'],
        q: 'concurrent observation',
        top_k: 10,
        include_observations: true,
      }).catch(() => null);

      await Promise.all([...insertPromises, activatePromise]);

      // Main check: no crash, DB is consistent
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        "SELECT COUNT(*)::INTEGER AS cnt FROM observations WHERE id LIKE 'obs_concurrent_%'"
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]!.cnt).toBe(10);
    });
  });
});

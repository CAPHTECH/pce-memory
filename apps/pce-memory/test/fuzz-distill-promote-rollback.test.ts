/**
 * Fuzz testing for pce_memory_distill, pce_memory_promote, and pce_memory_rollback handlers.
 */
import { beforeEach, describe, it } from 'vitest';
import {
  applyPolicy,
  createObservation,
  createPendingCandidate,
  createPromotedClaim,
  dispatchTool,
  expectError,
  expectSuccess,
  setupRuntime,
  validProvenance,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
});

describe('FUZZ: pce_memory_distill', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects when no sources provided', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {}),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-array source_observation_ids', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: 'obs_123',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects source_observation_ids with non-string items', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [42, 'obs_123'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent observation IDs', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: ['obs_nonexistent'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent claim IDs', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_claim_ids: ['clm_nonexistent'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid proposed_kind', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_kind: 'invalid_kind',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid proposed_scope', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_scope: 'session',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects proposed_memory_type=evidence', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_memory_type: 'evidence',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string active_context_id', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        active_context_id: 42,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string note', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        note: 42,
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_promote', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects empty candidate_id', async () => {
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: '',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent candidate_id', async () => {
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: 'pq_nonexistent',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing provenance', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects promote on already-promoted candidate', async () => {
    const { candidate } = await createPromotedClaim();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string review_note', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        review_note: 42,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-array reviewers', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        reviewers: 'alice',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects reviewers with non-string entries', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        reviewers: [42],
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_rollback', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects empty claim_id', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: '',
        reason: 'test',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects empty reason', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_123',
        reason: '',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent claim_id', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_nonexistent',
        reason: 'test',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects rollback on already-rolled-back claim', async () => {
    const { promote } = await createPromotedClaim();
    // First rollback
    expectSuccess(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'first rollback',
        provenance: validProvenance(),
      })
    );
    // Second rollback should fail
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'second rollback',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing provenance', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_123',
        reason: 'test',
      }),
      'VALIDATION_ERROR'
    );
  });
});

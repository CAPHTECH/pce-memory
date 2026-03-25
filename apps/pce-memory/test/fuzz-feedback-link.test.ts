/**
 * Fuzz testing for pce_memory_feedback and pce_memory_link_claims handlers.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  applyPolicy,
  createActivatedState,
  createClaim,
  dispatchTool,
  expectError,
  expectSuccess,
  setupRuntime,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
});

describe('FUZZ: pce_memory_feedback', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects feedback on non-existent claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: 'clm_nonexistent',
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid signal', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
        signal: 'invalid_signal',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing signal', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects null claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: null,
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects empty string claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: '',
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('handles score=NaN gracefully', async () => {
    const claim = await createActivatedState();
    // NaN score should not crash
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: NaN,
    });
    expect(result).toBeDefined();
  });

  it('handles score=Infinity gracefully', async () => {
    const claim = await createActivatedState();
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: Infinity,
    });
    expect(result).toBeDefined();
  });

  it('handles negative score gracefully', async () => {
    const claim = await createActivatedState();
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: -1,
    });
    expect(result).toBeDefined();
  });

  it('rejects completed signal on non-working_state claim', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
        signal: 'completed',
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_link_claims', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects link with same source and target', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim.id,
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects link with non-existent source', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: 'clm_nonexistent',
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects link with non-existent target', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim.id,
        target_claim_id: 'clm_nonexistent',
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid link_type', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'invalid_type',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing source_claim_id', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects confidence > 1', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 1.5,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects confidence < 0', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: -0.5,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects NaN confidence', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: NaN,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('accepts confidence=0 (boundary)', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectSuccess(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 0,
      })
    );
  });

  it('accepts confidence=1 (boundary)', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectSuccess(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 1,
      })
    );
  });
});

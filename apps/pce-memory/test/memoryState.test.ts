/**
 * state/memoryState.ts のテスト
 * モジュールレベル状態管理の未カバー部分
 */
import { describe, it, expect, beforeEach } from 'vitest';
import * as E from 'fp-ts/Either';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState } from '../src/store/rate';
import {
  resetMemoryState,
  getPolicy,
  getRetrievalPolicy,
  getMaintenancePolicy,
  getPolicyVersion,
  getStateType,
  getRuntimeState,
  canDoUpsert,
  canDoActivate,
  canDoFeedback,
  canDoQuery,
  getClaimCount,
  getActiveContextId,
  initMemoryState,
  applyPolicyOp,
  transitionToHasClaims,
  transitionToReady,
  getStateSummary,
} from '../src/state/memoryState';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
  resetMemoryState();
});

describe('initial state accessors', () => {
  it('starts in Uninitialized state', () => {
    expect(getStateType()).toBe('Uninitialized');
  });

  it('returns default policy', () => {
    const policy = getPolicy();
    expect(policy).toBeDefined();
  });

  it('returns default retrieval policy', () => {
    const policy = getRetrievalPolicy();
    expect(policy).toBeDefined();
  });

  it('returns default maintenance policy', () => {
    const policy = getMaintenancePolicy();
    expect(policy).toBeDefined();
  });

  it('getPolicyVersion returns default version for Uninitialized', () => {
    // Uninitialized state returns a default version string
    expect(typeof getPolicyVersion()).toBe('string');
  });

  it('getRuntimeState returns Uninitialized', () => {
    expect(getRuntimeState().type).toBe('Uninitialized');
  });

  it('canDoUpsert is false in Uninitialized', () => {
    expect(canDoUpsert()).toBe(false);
  });

  it('canDoActivate is false in Uninitialized', () => {
    expect(canDoActivate()).toBe(false);
  });

  it('canDoFeedback is false in Uninitialized', () => {
    expect(canDoFeedback()).toBe(false);
  });

  it('canDoQuery is false in Uninitialized', () => {
    expect(canDoQuery()).toBe(false);
  });

  it('getClaimCount is 0 in Uninitialized', () => {
    expect(getClaimCount()).toBe(0);
  });

  it('getActiveContextId is undefined in Uninitialized', () => {
    expect(getActiveContextId()).toBeUndefined();
  });
});

describe('initMemoryState', () => {
  it('restores state from DB (no stored policy → Uninitialized)', async () => {
    const result = await initMemoryState()();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.state).toBe('Uninitialized');
    }
  });

  it('restores PolicyApplied if policy was saved', async () => {
    // Apply policy first
    const applyResult = await applyPolicyOp()();
    expect(E.isRight(applyResult)).toBe(true);

    // Reset in-memory state
    resetMemoryState();

    // Re-init from DB
    const result = await initMemoryState()();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.state).toBe('PolicyApplied');
    }
  });
});

describe('applyPolicyOp', () => {
  it('transitions from Uninitialized to PolicyApplied', async () => {
    const result = await applyPolicyOp()();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.state).toBe('PolicyApplied');
      expect(result.right.policy_version).toBeDefined();
    }
    expect(getStateType()).toBe('PolicyApplied');
    expect(canDoUpsert()).toBe(true);
    expect(canDoActivate()).toBe(true);
  });

  it('returns STATE_ERROR if already PolicyApplied', async () => {
    await applyPolicyOp()();
    const result = await applyPolicyOp()();
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('STATE_ERROR');
      expect(result.left.message).toContain('expected Uninitialized');
    }
  });

  it('returns POLICY_INVALID for malformed yaml', async () => {
    const result = await applyPolicyOp('not: {valid: yaml: policy')();
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('POLICY_INVALID');
    }
  });
});

describe('transitionToHasClaims', () => {
  it('transitions to HasClaims after upsert', async () => {
    await applyPolicyOp()();
    transitionToHasClaims(true);
    expect(getStateType()).toBe('HasClaims');
    expect(getClaimCount()).toBe(1);
  });

  it('increments count for new claims', async () => {
    await applyPolicyOp()();
    transitionToHasClaims(true);
    transitionToHasClaims(true);
    expect(getClaimCount()).toBe(2);
  });

  it('does not increment for duplicate claims (isNew=false)', async () => {
    await applyPolicyOp()();
    transitionToHasClaims(true);
    transitionToHasClaims(false);
    expect(getClaimCount()).toBe(1);
  });
});

describe('transitionToReady', () => {
  it('transitions to Ready with activeContextId', async () => {
    await applyPolicyOp()();
    transitionToHasClaims(true);
    transitionToReady('ac_test123');
    expect(getStateType()).toBe('Ready');
    expect(getActiveContextId()).toBe('ac_test123');
    expect(canDoFeedback()).toBe(true);
  });
});

describe('getStateSummary', () => {
  it('returns basic summary without details', () => {
    const summary = getStateSummary();
    expect(summary.state).toBe('Uninitialized');
    expect(typeof summary.policy_version).toBe('string');
    expect(summary.runtime_state).toBeUndefined();
  });

  it('returns detailed summary with runtime_state', () => {
    const summary = getStateSummary(true);
    expect(summary.state).toBe('Uninitialized');
    expect(summary.runtime_state).toBeDefined();
    expect(summary.runtime_state!.type).toBe('Uninitialized');
  });

  it('includes policy version after apply', async () => {
    await applyPolicyOp()();
    const summary = getStateSummary(true);
    expect(summary.state).toBe('PolicyApplied');
    expect(summary.policy_version).toBeDefined();
    expect(summary.runtime_state!.type).toBe('PolicyApplied');
  });
});

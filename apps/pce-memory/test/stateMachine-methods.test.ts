/**
 * domain/stateMachine.ts の追加テスト
 * PCEMemory クラスの状態遷移メソッド（lines 139-235）のカバレッジ
 */
import { describe, it, expect } from 'vitest';
import * as E from 'fp-ts/Either';
import * as TE from 'fp-ts/TaskEither';
import { PCEMemory, stateError } from '../src/domain/stateMachine';
import type {
  ClaimInput,
  ActivateInput,
  FeedbackInput,
  HasClaims,
  PolicyApplied,
  Ready,
} from '../src/domain/stateMachine';
import { domainError } from '../src/domain/errors';

describe('PCEMemory.applyPolicy', () => {
  it('transitions Uninitialized → PolicyApplied on success', async () => {
    const machine = PCEMemory.create();
    const applyFn = () => E.right('1.0');

    const result = await machine.applyPolicy({}, applyFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.result.policyVersion).toBe('1.0');
      expect(result.right.machine.getStateType()).toBe('PolicyApplied');
      expect(result.right.machine.getPolicyVersion()).toBe('1.0');
    }
  });

  it('returns Left when applyFn fails', async () => {
    const machine = PCEMemory.create();
    const applyFn = () => E.left(domainError('POLICY_INVALID', 'bad policy'));

    const result = await machine.applyPolicy({}, applyFn)();
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('POLICY_INVALID');
    }
  });

  it('passes yaml to applyFn', async () => {
    const machine = PCEMemory.create();
    let receivedYaml: string | undefined;
    const applyFn = (yaml?: string) => {
      receivedYaml = yaml;
      return E.right('2.0');
    };

    await machine.applyPolicy({ yaml: 'custom: policy' }, applyFn)();
    expect(receivedYaml).toBe('custom: policy');
  });
});

describe('PCEMemory.upsert', () => {
  const claimInput: ClaimInput = {
    text: 'test claim',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: `sha256:${'a'.repeat(64)}`,
  };

  it('transitions PolicyApplied → HasClaims with isNew=true', async () => {
    const machine = PCEMemory.restore({
      type: 'PolicyApplied',
      policyVersion: '1.0',
    });
    const upsertFn = () => TE.right({ id: 'clm_001', isNew: true });

    const result = await (machine as PCEMemory<PolicyApplied>).upsert(claimInput, upsertFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.result.id).toBe('clm_001');
      expect(result.right.result.isNew).toBe(true);
      expect(result.right.result.policyVersion).toBe('1.0');
      expect(result.right.machine.getStateType()).toBe('HasClaims');
      expect(result.right.machine.getClaimCount()).toBe(1);
    }
  });

  it('maintains count for duplicate (isNew=false)', async () => {
    const machine = PCEMemory.restore({
      type: 'HasClaims',
      policyVersion: '1.0',
      claimCount: 5,
    });
    const upsertFn = () => TE.right({ id: 'clm_002', isNew: false });

    const result = await (machine as PCEMemory<PolicyApplied>).upsert(claimInput, upsertFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.machine.getClaimCount()).toBe(5);
    }
  });

  it('increments count for new claim in HasClaims state', async () => {
    const machine = PCEMemory.restore({
      type: 'HasClaims',
      policyVersion: '1.0',
      claimCount: 3,
    });
    const upsertFn = () => TE.right({ id: 'clm_003', isNew: true });

    const result = await (machine as PCEMemory<PolicyApplied>).upsert(claimInput, upsertFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.machine.getClaimCount()).toBe(4);
    }
  });

  it('returns Left when upsertFn fails', async () => {
    const machine = PCEMemory.restore({
      type: 'PolicyApplied',
      policyVersion: '1.0',
    });
    const upsertFn = () => TE.left(domainError('UPSERT_FAILED', 'db error'));

    const result = await (machine as PCEMemory<PolicyApplied>).upsert(claimInput, upsertFn)();
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('UPSERT_FAILED');
    }
  });

  it('guarantees minimum claimCount of 1 for first duplicate from PolicyApplied', async () => {
    const machine = PCEMemory.restore({
      type: 'PolicyApplied',
      policyVersion: '1.0',
    });
    const upsertFn = () => TE.right({ id: 'clm_dup', isNew: false });

    const result = await (machine as PCEMemory<PolicyApplied>).upsert(claimInput, upsertFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // Math.max(0, 1) = 1 for first duplicate from PolicyApplied (count=0)
      expect(result.right.machine.getClaimCount()).toBe(1);
    }
  });
});

describe('PCEMemory.activate', () => {
  const activateInput: ActivateInput = {
    scope: ['project'],
    allow: ['answer:task'],
    top_k: 10,
  };

  it('transitions HasClaims → Ready', async () => {
    const machine = PCEMemory.restore({
      type: 'HasClaims',
      policyVersion: '1.0',
      claimCount: 5,
    });
    const activateFn = () => TE.right({ id: 'ac_001', claims: [{ id: 'clm_1' }] });

    const result = await (machine as PCEMemory<HasClaims>).activate(activateInput, activateFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.result.activeContextId).toBe('ac_001');
      expect(result.right.result.claims).toHaveLength(1);
      expect(result.right.result.policyVersion).toBe('1.0');
      expect(result.right.machine.getStateType()).toBe('Ready');
      expect(result.right.machine.getActiveContextId()).toBe('ac_001');
    }
  });

  it('returns Left when activateFn fails', async () => {
    const machine = PCEMemory.restore({
      type: 'HasClaims',
      policyVersion: '1.0',
      claimCount: 1,
    });
    const activateFn = () => TE.left(domainError('ACTIVATE_FAILED', 'search error'));

    const result = await (machine as PCEMemory<HasClaims>).activate(activateInput, activateFn)();
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('PCEMemory.feedback', () => {
  const feedbackInput: FeedbackInput = {
    claim_id: 'clm_001',
    signal: 'helpful',
  };

  it('stays in Ready state after feedback', async () => {
    const machine = PCEMemory.restore({
      type: 'Ready',
      policyVersion: '1.0',
      activeContextId: 'ac_001',
    });
    const feedbackFn = () => TE.right({ id: 'fb_001' });

    const result = await (machine as PCEMemory<Ready>).feedback(feedbackInput, feedbackFn)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.result.id).toBe('fb_001');
      expect(result.right.result.policyVersion).toBe('1.0');
      expect(result.right.machine.getStateType()).toBe('Ready');
      expect(result.right.machine.getActiveContextId()).toBe('ac_001');
    }
  });

  it('returns Left when feedbackFn fails', async () => {
    const machine = PCEMemory.restore({
      type: 'Ready',
      policyVersion: '1.0',
      activeContextId: 'ac_001',
    });
    const feedbackFn = () => TE.left(domainError('FEEDBACK_FAILED', 'not found'));

    const result = await (machine as PCEMemory<Ready>).feedback(feedbackInput, feedbackFn)();
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('stateError', () => {
  it('creates error with expected/actual message', () => {
    const err = stateError('PolicyApplied', 'Uninitialized');
    expect(err.code).toBe('VALIDATION_ERROR');
    expect(err.message).toBe('Invalid state: expected PolicyApplied, got Uninitialized');
  });
});

describe('PCEMemory helper methods', () => {
  it('getPolicyVersion returns version for PolicyApplied', () => {
    const m = PCEMemory.restore({ type: 'PolicyApplied', policyVersion: '2.0' });
    expect(m.getPolicyVersion()).toBe('2.0');
  });

  it('getPolicyVersion returns 0.0 for Uninitialized', () => {
    const m = PCEMemory.create();
    expect(m.getPolicyVersion()).toBe('0.0');
  });

  it('getClaimCount returns count for HasClaims', () => {
    const m = PCEMemory.restore({ type: 'HasClaims', policyVersion: '1.0', claimCount: 42 });
    expect(m.getClaimCount()).toBe(42);
  });

  it('getClaimCount returns 0 for non-HasClaims', () => {
    const m = PCEMemory.restore({ type: 'PolicyApplied', policyVersion: '1.0' });
    expect(m.getClaimCount()).toBe(0);
  });

  it('getActiveContextId returns id for Ready', () => {
    const m = PCEMemory.restore({
      type: 'Ready',
      policyVersion: '1.0',
      activeContextId: 'ac_test',
    });
    expect(m.getActiveContextId()).toBe('ac_test');
  });

  it('getActiveContextId returns undefined for non-Ready', () => {
    const m = PCEMemory.restore({ type: 'HasClaims', policyVersion: '1.0', claimCount: 1 });
    expect(m.getActiveContextId()).toBeUndefined();
  });
});

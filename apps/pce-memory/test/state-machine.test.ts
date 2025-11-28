/**
 * 状態機械のテスト（ADR-0002）
 * 状態遷移と STATE_ERROR のテストカバレッジ
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDb } from '../src/db/connection';
import { initRateState, resetRates } from '../src/store/rate';

// テスト用のハンドラをimportするため、index.tsをモジュールとしてテスト
// 注: MCPサーバーは直接テストが難しいため、ストア層と状態機械ユーティリティをテスト

import {
  canUpsert,
  canActivate,
  canFeedback,
  stateError,
  isUninitialized,
  isPolicyApplied,
  isHasClaims,
  isReady,
  PCEMemory,
} from '../src/domain/stateMachine';
import type { RuntimeState } from '../src/domain/stateMachine';

describe('状態機械ユーティリティ関数', () => {
  describe('状態判定関数', () => {
    it('isUninitialized: Uninitialized状態を正しく判定', () => {
      const state: RuntimeState = { type: 'Uninitialized' };
      expect(isUninitialized(state)).toBe(true);
      expect(isPolicyApplied(state)).toBe(false);
    });

    it('isPolicyApplied: PolicyApplied状態を正しく判定', () => {
      const state: RuntimeState = { type: 'PolicyApplied', policyVersion: '1.0' };
      expect(isPolicyApplied(state)).toBe(true);
      expect(isUninitialized(state)).toBe(false);
    });

    it('isHasClaims: HasClaims状態を正しく判定', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 5 };
      expect(isHasClaims(state)).toBe(true);
      expect(isPolicyApplied(state)).toBe(false);
    });

    it('isReady: Ready状態を正しく判定', () => {
      const state: RuntimeState = {
        type: 'Ready',
        policyVersion: '1.0',
        activeContextId: 'ac_123',
      };
      expect(isReady(state)).toBe(true);
      expect(isHasClaims(state)).toBe(false);
    });
  });

  describe('状態遷移可能性チェック関数', () => {
    it('canUpsert: PolicyApplied状態でtrue', () => {
      const state: RuntimeState = { type: 'PolicyApplied', policyVersion: '1.0' };
      expect(canUpsert(state)).toBe(true);
    });

    it('canUpsert: HasClaims状態でtrue', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 1 };
      expect(canUpsert(state)).toBe(true);
    });

    it('canUpsert: Uninitialized状態でfalse', () => {
      const state: RuntimeState = { type: 'Uninitialized' };
      expect(canUpsert(state)).toBe(false);
    });

    it('canUpsert: Ready状態でtrue（追加upsert可能）', () => {
      const state: RuntimeState = {
        type: 'Ready',
        policyVersion: '1.0',
        activeContextId: 'ac_123',
      };
      expect(canUpsert(state)).toBe(true);
    });

    it('canActivate: HasClaims状態でtrue', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 1 };
      expect(canActivate(state)).toBe(true);
    });

    it('canActivate: Uninitialized状態でfalse', () => {
      const state: RuntimeState = { type: 'Uninitialized' };
      expect(canActivate(state)).toBe(false);
    });

    it('canFeedback: Ready状態でtrue', () => {
      const state: RuntimeState = {
        type: 'Ready',
        policyVersion: '1.0',
        activeContextId: 'ac_123',
      };
      expect(canFeedback(state)).toBe(true);
    });

    it('canFeedback: HasClaims状態でfalse', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 1 };
      expect(canFeedback(state)).toBe(false);
    });
  });

  describe('stateError関数', () => {
    it('期待状態と実際の状態を含むエラーを生成', () => {
      const error = stateError('PolicyApplied', 'Uninitialized');
      expect(error._tag).toBe('DomainError');
      expect(error.code).toBe('VALIDATION_ERROR');
      expect(error.message).toContain('PolicyApplied');
      expect(error.message).toContain('Uninitialized');
    });
  });
});

describe('PCEMemoryクラス', () => {
  describe('ファクトリメソッド', () => {
    it('create: Uninitialized状態で初期化', () => {
      const machine = PCEMemory.create();
      expect(machine.getStateType()).toBe('Uninitialized');
      expect(machine.getPolicyVersion()).toBe('0.0');
    });

    it('restore: RuntimeStateから復元', () => {
      const state: RuntimeState = {
        type: 'Ready',
        policyVersion: '2.0',
        activeContextId: 'ac_test',
      };
      const machine = PCEMemory.restore(state);
      expect(machine.getStateType()).toBe('Ready');
      expect(machine.getPolicyVersion()).toBe('2.0');
      expect(machine.getActiveContextId()).toBe('ac_test');
    });
  });

  describe('ヘルパーメソッド', () => {
    it('getClaimCount: HasClaims状態でclaimCountを返す', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 42 };
      const machine = PCEMemory.restore(state);
      expect(machine.getClaimCount()).toBe(42);
    });

    it('getClaimCount: 他の状態では0を返す', () => {
      const state: RuntimeState = { type: 'PolicyApplied', policyVersion: '1.0' };
      const machine = PCEMemory.restore(state);
      expect(machine.getClaimCount()).toBe(0);
    });

    it('getActiveContextId: Ready状態でactiveContextIdを返す', () => {
      const state: RuntimeState = {
        type: 'Ready',
        policyVersion: '1.0',
        activeContextId: 'ac_xyz',
      };
      const machine = PCEMemory.restore(state);
      expect(machine.getActiveContextId()).toBe('ac_xyz');
    });

    it('getActiveContextId: 他の状態ではundefinedを返す', () => {
      const state: RuntimeState = { type: 'HasClaims', policyVersion: '1.0', claimCount: 1 };
      const machine = PCEMemory.restore(state);
      expect(machine.getActiveContextId()).toBeUndefined();
    });
  });
});

describe('状態遷移のE2Eシナリオ', () => {
  beforeEach(async () => {
    resetDb();
    process.env.PCE_DB = ':memory:';
    process.env.PCE_RATE_CAP = '100';
    await initDb();
    await initSchema();
    await initRateState();
    await resetRates();
  });

  it('正常フロー: Uninitialized → PolicyApplied → HasClaims → Ready', () => {
    // このテストはドメイン層の状態遷移ロジックを検証
    // 実際のMCPハンドラを経由するテストは別途Integration Testとして実装が必要

    // 1. 初期状態
    let state: RuntimeState = { type: 'Uninitialized' };
    expect(isUninitialized(state)).toBe(true);
    expect(canUpsert(state)).toBe(false);

    // 2. PolicyApplied
    state = { type: 'PolicyApplied', policyVersion: '1.0' };
    expect(isPolicyApplied(state)).toBe(true);
    expect(canUpsert(state)).toBe(true);
    expect(canActivate(state)).toBe(false);

    // 3. HasClaims
    state = { type: 'HasClaims', policyVersion: '1.0', claimCount: 1 };
    expect(isHasClaims(state)).toBe(true);
    expect(canUpsert(state)).toBe(true); // 追加upsert可能
    expect(canActivate(state)).toBe(true);
    expect(canFeedback(state)).toBe(false);

    // 4. Ready
    state = { type: 'Ready', policyVersion: '1.0', activeContextId: 'ac_test' };
    expect(isReady(state)).toBe(true);
    expect(canUpsert(state)).toBe(true); // Ready状態からも追加upsert可能
    expect(canFeedback(state)).toBe(true);
  });

  it('不正な状態遷移: Uninitializedからactivateは不可', () => {
    const state: RuntimeState = { type: 'Uninitialized' };
    expect(canActivate(state)).toBe(false);
  });

  it('不正な状態遷移: PolicyAppliedからfeedbackは不可', () => {
    const state: RuntimeState = { type: 'PolicyApplied', policyVersion: '1.0' };
    expect(canFeedback(state)).toBe(false);
  });
});

describe('countClaims関数', () => {
  beforeEach(async () => {
    resetDb();
    process.env.PCE_DB = ':memory:';
    await initDb();
    await initSchema();
  });

  it('空のDBでは0を返す', async () => {
    const { countClaims } = await import('../src/store/claims');
    const count = await countClaims();
    expect(count).toBe(0);
  });

  it('claimを登録後は正しいカウントを返す', async () => {
    const { countClaims, upsertClaim } = await import('../src/store/claims');
    // 3つのclaimを登録
    await upsertClaim({
      text: 'test1',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'public',
      content_hash: 'sha256:' + 'a'.repeat(64),
    });
    await upsertClaim({
      text: 'test2',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'public',
      content_hash: 'sha256:' + 'b'.repeat(64),
    });
    await upsertClaim({
      text: 'test3',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'public',
      content_hash: 'sha256:' + 'c'.repeat(64),
    });

    const count = await countClaims();
    expect(count).toBe(3);
  });
});

describe('PCEMemory.restore状態復元', () => {
  it('HasClaims状態から復元', () => {
    const state: RuntimeState = {
      type: 'HasClaims',
      policyVersion: '1.2',
      claimCount: 10,
    };
    const machine = PCEMemory.restore(state);
    expect(machine.getStateType()).toBe('HasClaims');
    expect(machine.getPolicyVersion()).toBe('1.2');
    expect(machine.getClaimCount()).toBe(10);
  });

  it('PolicyApplied状態から復元', () => {
    const state: RuntimeState = {
      type: 'PolicyApplied',
      policyVersion: '2.0',
    };
    const machine = PCEMemory.restore(state);
    expect(machine.getStateType()).toBe('PolicyApplied');
    expect(machine.getPolicyVersion()).toBe('2.0');
    expect(machine.getClaimCount()).toBe(0);
  });
});

describe('重複upsertとisNewフラグ', () => {
  beforeEach(async () => {
    resetDb();
    process.env.PCE_DB = ':memory:';
    await initDb();
    await initSchema();
  });

  it('新規upsertはisNew=trueを返す', async () => {
    const { upsertClaim } = await import('../src/store/claims');
    const { claim, isNew } = await upsertClaim({
      text: 'new claim',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'public',
      content_hash: 'sha256:' + 'x'.repeat(64),
    });
    expect(isNew).toBe(true);
    expect(claim.id).toBeDefined();
  });

  it('重複upsertはisNew=falseを返す', async () => {
    const { upsertClaim } = await import('../src/store/claims');
    const hash = 'sha256:' + 'y'.repeat(64);

    // 最初の挿入
    const { claim: first, isNew: isFirstNew } = await upsertClaim({
      text: 'original',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'public',
      content_hash: hash,
    });
    expect(isFirstNew).toBe(true);

    // 同じhashで再度upsert
    const { claim: second, isNew: isSecondNew } = await upsertClaim({
      text: 'duplicate attempt',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'public',
      content_hash: hash,
    });
    expect(isSecondNew).toBe(false);
    expect(second.id).toBe(first.id); // 同じidを返す
  });
});

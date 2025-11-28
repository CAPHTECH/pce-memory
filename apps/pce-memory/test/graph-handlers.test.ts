/**
 * Graph Memory MCP Handler Tests
 * handleUpsertEntity, handleUpsertRelation のテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState, resetRates } from '../src/store/rate';
import { handleUpsertEntity, handleUpsertRelation } from '../src/core/handlers';
import { applyPolicyOp, resetMemoryState } from '../src/state/memoryState';
import * as E from 'fp-ts/Either';

/**
 * 標準的なテストセットアップ: DB初期化 + PolicyApplied状態
 */
async function setupWithPolicy() {
  await resetDbAsync();
  resetMemoryState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  const result = await applyPolicyOp()();
  expect(E.isRight(result)).toBe(true);
}

/**
 * Uninitialized状態のセットアップ（ポリシー未適用）
 */
async function setupWithoutPolicy() {
  await resetDbAsync();
  resetMemoryState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

beforeEach(async () => {
  await setupWithPolicy();
});

describe('handleUpsertEntity', () => {
  it('creates a new entity successfully', async () => {
    const result = await handleUpsertEntity({
      id: 'ent_test_001',
      type: 'Actor',
      name: 'Test Actor',
    });

    expect(result.isError).toBeUndefined();
    const response = JSON.parse(result.content[0]!.text);
    expect(response.id).toBe('ent_test_001');
    expect(response.type).toBe('Actor');
    expect(response.name).toBe('Test Actor');
    expect(response.policy_version).toBeDefined();
    expect(response.state).toBeDefined();
  });

  it('creates entity with optional fields', async () => {
    const result = await handleUpsertEntity({
      id: 'ent_test_002',
      type: 'Artifact',
      name: 'Test Artifact',
      canonical_key: 'test-key',
      attrs: { version: '1.0', language: 'typescript' },
    });

    expect(result.isError).toBeUndefined();
    const response = JSON.parse(result.content[0]!.text);
    expect(response.id).toBe('ent_test_002');
    expect(response.canonical_key).toBe('test-key');
  });

  it('returns error for missing required fields', async () => {
    const result = await handleUpsertEntity({
      id: 'ent_test_003',
      type: 'Actor',
      // name is missing
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('VALIDATION_ERROR');
  });

  it('returns error for invalid type', async () => {
    const result = await handleUpsertEntity({
      id: 'ent_test_004',
      type: 'InvalidType',
      name: 'Test',
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('VALIDATION_ERROR');
  });

  it('is idempotent - returns existing entity on duplicate', async () => {
    const first = await handleUpsertEntity({
      id: 'ent_dup',
      type: 'Concept',
      name: 'Original',
    });
    const second = await handleUpsertEntity({
      id: 'ent_dup',
      type: 'Event',
      name: 'Modified',
    });

    const firstResponse = JSON.parse(first.content[0]!.text);
    const secondResponse = JSON.parse(second.content[0]!.text);

    expect(firstResponse.id).toBe(secondResponse.id);
    expect(secondResponse.type).toBe('Concept'); // 変更されない
    expect(secondResponse.name).toBe('Original'); // 変更されない
  });
});

describe('handleUpsertRelation', () => {
  it('creates a new relation successfully', async () => {
    const result = await handleUpsertRelation({
      id: 'rel_test_001',
      src_id: 'ent_a',
      dst_id: 'ent_b',
      type: 'KNOWS',
    });

    expect(result.isError).toBeUndefined();
    const response = JSON.parse(result.content[0]!.text);
    expect(response.id).toBe('rel_test_001');
    expect(response.src_id).toBe('ent_a');
    expect(response.dst_id).toBe('ent_b');
    expect(response.type).toBe('KNOWS');
  });

  it('creates relation with optional fields', async () => {
    const result = await handleUpsertRelation({
      id: 'rel_test_002',
      src_id: 'ent_x',
      dst_id: 'ent_y',
      type: 'DEPENDS_ON',
      props: { weight: 0.8, reason: 'direct dependency' },
      evidence_claim_id: 'clm_123',
    });

    expect(result.isError).toBeUndefined();
    const response = JSON.parse(result.content[0]!.text);
    expect(response.id).toBe('rel_test_002');
    expect(response.evidence_claim_id).toBe('clm_123');
  });

  it('returns error for missing required fields', async () => {
    const result = await handleUpsertRelation({
      id: 'rel_test_003',
      src_id: 'ent_a',
      // dst_id and type are missing
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('VALIDATION_ERROR');
  });

  it('is idempotent - returns existing relation on duplicate', async () => {
    const first = await handleUpsertRelation({
      id: 'rel_dup',
      src_id: 'a',
      dst_id: 'b',
      type: 'ORIGINAL',
    });
    const second = await handleUpsertRelation({
      id: 'rel_dup',
      src_id: 'x',
      dst_id: 'y',
      type: 'MODIFIED',
    });

    const firstResponse = JSON.parse(first.content[0]!.text);
    const secondResponse = JSON.parse(second.content[0]!.text);

    expect(firstResponse.id).toBe(secondResponse.id);
    expect(secondResponse.type).toBe('ORIGINAL'); // 変更されない
  });
});

describe('State and Rate Limit handling', () => {
  it('returns STATE_ERROR when policy is not applied for entity', async () => {
    await setupWithoutPolicy();

    const result = await handleUpsertEntity({
      id: 'ent_state_err',
      type: 'Actor',
      name: 'Test Actor',
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('STATE_ERROR');
  });

  it('returns STATE_ERROR when policy is not applied for relation', async () => {
    await setupWithoutPolicy();

    const result = await handleUpsertRelation({
      id: 'rel_state_err',
      src_id: 'a',
      dst_id: 'b',
      type: 'RELATES_TO',
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('STATE_ERROR');
  });

  it('returns RATE_LIMIT when rate limit exceeded for entity', async () => {
    // レート上限を1に設定し、1回消費して制限に到達させる
    const originalCap = process.env.PCE_RATE_CAP;
    process.env.PCE_RATE_CAP = '1';
    await initRateState();
    await resetRates();

    // 1回目は成功
    await handleUpsertEntity({
      id: 'ent_first',
      type: 'Actor',
      name: 'First Actor',
    });

    // 2回目でレート制限
    const result = await handleUpsertEntity({
      id: 'ent_rate_limit',
      type: 'Actor',
      name: 'Test Actor',
    });

    // 環境変数を元に戻す
    process.env.PCE_RATE_CAP = originalCap;

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('RATE_LIMIT');
  });

  it('returns RATE_LIMIT when rate limit exceeded for relation', async () => {
    // レート上限を1に設定し、1回消費して制限に到達させる
    const originalCap = process.env.PCE_RATE_CAP;
    process.env.PCE_RATE_CAP = '1';
    await initRateState();
    await resetRates();

    // 1回目は成功
    await handleUpsertRelation({
      id: 'rel_first',
      src_id: 'a',
      dst_id: 'b',
      type: 'FIRST',
    });

    // 2回目でレート制限
    const result = await handleUpsertRelation({
      id: 'rel_rate_limit',
      src_id: 'a',
      dst_id: 'b',
      type: 'RELATES_TO',
    });

    // 環境変数を元に戻す
    process.env.PCE_RATE_CAP = originalCap;

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('RATE_LIMIT');
  });
});

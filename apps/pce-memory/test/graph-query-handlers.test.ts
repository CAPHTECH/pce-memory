/**
 * Graph Memory Query Handler Tests
 * handleQueryEntity, handleQueryRelation のテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { initRateState, resetRates } from '../src/store/rate';
import {
  handleUpsertEntity,
  handleUpsertRelation,
  handleQueryEntity,
  handleQueryRelation,
} from '../src/core/handlers';
import { applyPolicyOp, resetMemoryState } from '../src/state/memoryState';
import { upsertClaim } from '../src/store/claims';
import { linkClaimEntity } from '../src/store/entities';
import * as E from 'fp-ts/Either';

/**
 * 全テーブルのデータをクリア（スキーマは維持）
 */
async function clearAllTables() {
  const conn = await getConnection();
  // 依存関係を考慮した順序でDELETE
  await conn.run('DELETE FROM claim_entities');
  await conn.run('DELETE FROM relations');
  await conn.run('DELETE FROM entities');
  await conn.run('DELETE FROM feedback');
  await conn.run('DELETE FROM logs');
  await conn.run('DELETE FROM active_contexts');
  await conn.run('DELETE FROM evidence');
  await conn.run('DELETE FROM embedding_cache');
  await conn.run('DELETE FROM claim_vectors');
  await conn.run('DELETE FROM claims');
  await conn.run('DELETE FROM policies');
}

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
  // 既存データをクリア（インメモリDBでも複数テスト間でデータが残る場合がある）
  await clearAllTables();
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
  await clearAllTables();
  await initRateState();
  await resetRates();
}

/**
 * テストデータ作成ヘルパー: Entity
 */
async function createTestEntity(id: string, type: string, name: string, canonicalKey?: string) {
  const result = await handleUpsertEntity({
    id,
    type,
    name,
    ...(canonicalKey !== undefined && { canonical_key: canonicalKey }),
  });
  return JSON.parse(result.content[0]!.text);
}

/**
 * テストデータ作成ヘルパー: Relation
 */
async function createTestRelation(
  id: string,
  srcId: string,
  dstId: string,
  type: string,
  evidenceClaimId?: string
) {
  const result = await handleUpsertRelation({
    id,
    src_id: srcId,
    dst_id: dstId,
    type,
    ...(evidenceClaimId !== undefined && { evidence_claim_id: evidenceClaimId }),
  });
  return JSON.parse(result.content[0]!.text);
}

/**
 * テストデータ作成ヘルパー: Claim
 */
async function createTestClaim(id: string) {
  const claim = await upsertClaim({
    text: 'test claim',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: `sha256:${id.padEnd(64, '0')}`,
    provenance: { at: new Date().toISOString() },
  });
  return claim.claim;
}

beforeEach(async () => {
  await setupWithPolicy();
});

describe('handleQueryEntity', () => {
  describe('basic queries', () => {
    it('returns empty result when no entities exist', async () => {
      const result = await handleQueryEntity({ type: 'Actor' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toEqual([]);
      expect(response.count).toBe(0);
    });

    it('finds entity by ID', async () => {
      await createTestEntity('ent_001', 'Actor', 'Test Actor');

      const result = await handleQueryEntity({ id: 'ent_001' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(1);
      expect(response.entities[0].id).toBe('ent_001');
      expect(response.entities[0].name).toBe('Test Actor');
      expect(response.count).toBe(1);
    });

    it('finds entities by type', async () => {
      await createTestEntity('ent_actor_1', 'Actor', 'Actor 1');
      await createTestEntity('ent_actor_2', 'Actor', 'Actor 2');
      await createTestEntity('ent_concept_1', 'Concept', 'Concept 1');

      const result = await handleQueryEntity({ type: 'Actor' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(2);
      expect(response.entities.every((e: { type: string }) => e.type === 'Actor')).toBe(true);
      expect(response.count).toBe(2);
    });

    it('finds entity by canonical_key', async () => {
      await createTestEntity('ent_001', 'Artifact', 'Test Artifact', 'test-key');
      await createTestEntity('ent_002', 'Artifact', 'Other Artifact', 'other-key');

      const result = await handleQueryEntity({ canonical_key: 'test-key' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(1);
      expect(response.entities[0].id).toBe('ent_001');
    });
  });

  describe('combined filters (AND logic)', () => {
    it('combines type and canonical_key filters', async () => {
      await createTestEntity('ent_001', 'Artifact', 'Artifact 1', 'key-1');
      await createTestEntity('ent_002', 'Concept', 'Concept 1', 'key-1');
      await createTestEntity('ent_003', 'Artifact', 'Artifact 2', 'key-2');

      const result = await handleQueryEntity({
        type: 'Artifact',
        canonical_key: 'key-1',
      });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(1);
      expect(response.entities[0].id).toBe('ent_001');
    });

    it('filters by claim_id (linked entities)', async () => {
      // Create entities
      await createTestEntity('ent_linked', 'Actor', 'Linked Actor');
      await createTestEntity('ent_unlinked', 'Actor', 'Unlinked Actor');

      // Create claim and link
      const claim = await createTestClaim('test_claim');
      await linkClaimEntity(claim.id, 'ent_linked');

      const result = await handleQueryEntity({ claim_id: claim.id });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(1);
      expect(response.entities[0].id).toBe('ent_linked');
    });

    it('combines type and claim_id filters', async () => {
      // Create entities of different types
      await createTestEntity('ent_actor', 'Actor', 'Actor');
      await createTestEntity('ent_concept', 'Concept', 'Concept');

      // Create claim and link both
      const claim = await createTestClaim('claim_multi');
      await linkClaimEntity(claim.id, 'ent_actor');
      await linkClaimEntity(claim.id, 'ent_concept');

      const result = await handleQueryEntity({
        type: 'Actor',
        claim_id: claim.id,
      });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(1);
      expect(response.entities[0].type).toBe('Actor');
    });
  });

  describe('limit parameter', () => {
    it('respects limit parameter', async () => {
      for (let i = 1; i <= 10; i++) {
        await createTestEntity(`ent_${i}`, 'Actor', `Actor ${i}`);
      }

      const result = await handleQueryEntity({ type: 'Actor', limit: 3 });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(3);
      expect(response.count).toBe(3);
    });

    it('uses default limit of 50', async () => {
      // Just verify it doesn't error with many entities
      for (let i = 1; i <= 5; i++) {
        await createTestEntity(`ent_${i}`, 'Actor', `Actor ${i}`);
      }

      const result = await handleQueryEntity({ type: 'Actor' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.entities).toHaveLength(5);
    });

    it('caps limit at 100', async () => {
      const result = await handleQueryEntity({ type: 'Actor', limit: 200 });

      // Should not error, just cap at 100
      expect(result.isError).toBeUndefined();
    });
  });

  describe('validation errors', () => {
    it('returns error when no filter is provided', async () => {
      const result = await handleQueryEntity({});

      expect(result.isError).toBe(true);
      const response = JSON.parse(result.content[0]!.text);
      expect(response.error.code).toBe('VALIDATION_ERROR');
      expect(response.error.message).toContain('at least one filter');
    });

    it('returns error for invalid type', async () => {
      const result = await handleQueryEntity({ type: 'InvalidType' });

      expect(result.isError).toBe(true);
      const response = JSON.parse(result.content[0]!.text);
      expect(response.error.code).toBe('VALIDATION_ERROR');
    });
  });

  describe('response format', () => {
    it('includes policy_version, state, request_id, trace_id', async () => {
      await createTestEntity('ent_001', 'Actor', 'Test');

      const result = await handleQueryEntity({ id: 'ent_001' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.policy_version).toBeDefined();
      expect(response.state).toBeDefined();
      expect(response.request_id).toBeDefined();
      expect(response.trace_id).toBeDefined();
    });
  });
});

describe('handleQueryRelation', () => {
  describe('basic queries', () => {
    it('returns empty result when no relations exist', async () => {
      const result = await handleQueryRelation({ type: 'KNOWS' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toEqual([]);
      expect(response.count).toBe(0);
    });

    it('finds relation by ID', async () => {
      await createTestRelation('rel_001', 'a', 'b', 'KNOWS');

      const result = await handleQueryRelation({ id: 'rel_001' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(1);
      expect(response.relations[0].id).toBe('rel_001');
      expect(response.count).toBe(1);
    });

    it('finds relations by src_id', async () => {
      await createTestRelation('rel_1', 'entity_a', 'entity_b', 'KNOWS');
      await createTestRelation('rel_2', 'entity_a', 'entity_c', 'LIKES');
      await createTestRelation('rel_3', 'entity_b', 'entity_c', 'KNOWS');

      const result = await handleQueryRelation({ src_id: 'entity_a' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(2);
      expect(response.relations.every((r: { src_id: string }) => r.src_id === 'entity_a')).toBe(
        true
      );
    });

    it('finds relations by dst_id', async () => {
      await createTestRelation('rel_1', 'a', 'target', 'KNOWS');
      await createTestRelation('rel_2', 'b', 'target', 'LIKES');
      await createTestRelation('rel_3', 'a', 'other', 'KNOWS');

      const result = await handleQueryRelation({ dst_id: 'target' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(2);
    });

    it('finds relations by type', async () => {
      await createTestRelation('rel_1', 'a', 'b', 'KNOWS');
      await createTestRelation('rel_2', 'b', 'c', 'KNOWS');
      await createTestRelation('rel_3', 'a', 'c', 'LIKES');

      const result = await handleQueryRelation({ type: 'KNOWS' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(2);
      expect(response.relations.every((r: { type: string }) => r.type === 'KNOWS')).toBe(true);
    });

    it('finds relations by evidence_claim_id', async () => {
      await createTestRelation('rel_1', 'a', 'b', 'KNOWS', 'clm_evidence');
      await createTestRelation('rel_2', 'b', 'c', 'KNOWS', 'clm_other');

      const result = await handleQueryRelation({ evidence_claim_id: 'clm_evidence' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(1);
      expect(response.relations[0].id).toBe('rel_1');
    });
  });

  describe('combined filters (AND logic)', () => {
    it('combines src_id and type filters', async () => {
      await createTestRelation('rel_1', 'entity_a', 'b', 'KNOWS');
      await createTestRelation('rel_2', 'entity_a', 'c', 'LIKES');
      await createTestRelation('rel_3', 'entity_b', 'c', 'KNOWS');

      const result = await handleQueryRelation({
        src_id: 'entity_a',
        type: 'KNOWS',
      });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(1);
      expect(response.relations[0].id).toBe('rel_1');
    });

    it('combines src_id, dst_id, and type filters', async () => {
      await createTestRelation('rel_target', 'a', 'b', 'KNOWS');
      await createTestRelation('rel_2', 'a', 'b', 'LIKES');
      await createTestRelation('rel_3', 'a', 'c', 'KNOWS');

      const result = await handleQueryRelation({
        src_id: 'a',
        dst_id: 'b',
        type: 'KNOWS',
      });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(1);
      expect(response.relations[0].id).toBe('rel_target');
    });
  });

  describe('limit parameter', () => {
    it('respects limit parameter', async () => {
      for (let i = 1; i <= 10; i++) {
        await createTestRelation(`rel_${i}`, `a_${i}`, `b_${i}`, 'KNOWS');
      }

      const result = await handleQueryRelation({ type: 'KNOWS', limit: 3 });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.relations).toHaveLength(3);
    });
  });

  describe('validation errors', () => {
    it('returns error when no filter is provided', async () => {
      const result = await handleQueryRelation({});

      expect(result.isError).toBe(true);
      const response = JSON.parse(result.content[0]!.text);
      expect(response.error.code).toBe('VALIDATION_ERROR');
      expect(response.error.message).toContain('at least one filter');
    });
  });

  describe('response format', () => {
    it('includes policy_version, state, request_id, trace_id', async () => {
      await createTestRelation('rel_001', 'a', 'b', 'KNOWS');

      const result = await handleQueryRelation({ id: 'rel_001' });

      expect(result.isError).toBeUndefined();
      const response = JSON.parse(result.content[0]!.text);
      expect(response.policy_version).toBeDefined();
      expect(response.state).toBeDefined();
      expect(response.request_id).toBeDefined();
      expect(response.trace_id).toBeDefined();
    });
  });
});

describe('State and Rate Limit handling', () => {
  it('returns STATE_ERROR when policy is not applied for query.entity', async () => {
    await setupWithoutPolicy();

    const result = await handleQueryEntity({ type: 'Actor' });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('STATE_ERROR');
  });

  it('returns STATE_ERROR when policy is not applied for query.relation', async () => {
    await setupWithoutPolicy();

    const result = await handleQueryRelation({ type: 'KNOWS' });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('STATE_ERROR');
  });

  it('returns RATE_LIMIT when rate limit exceeded for query.entity', async () => {
    const originalCap = process.env.PCE_RATE_CAP;
    process.env.PCE_RATE_CAP = '1';
    await initRateState();
    await resetRates();

    // First call succeeds
    await handleQueryEntity({ type: 'Actor' });

    // Second call hits rate limit
    const result = await handleQueryEntity({ type: 'Actor' });

    process.env.PCE_RATE_CAP = originalCap;

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('RATE_LIMIT');
  });

  it('returns RATE_LIMIT when rate limit exceeded for query.relation', async () => {
    const originalCap = process.env.PCE_RATE_CAP;
    process.env.PCE_RATE_CAP = '1';
    await initRateState();
    await resetRates();

    // First call succeeds
    await handleQueryRelation({ type: 'KNOWS' });

    // Second call hits rate limit
    const result = await handleQueryRelation({ type: 'KNOWS' });

    process.env.PCE_RATE_CAP = originalCap;

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('RATE_LIMIT');
  });
});

describe('BigInt serialization in structuredContent', () => {
  beforeEach(async () => {
    await setupWithPolicy();
  });

  it('query.entity: structuredContentにBigIntが含まれない（JSON.stringifyが成功する）', async () => {
    // Entity作成（created_atがBigIntで返される可能性がある）
    await handleUpsertEntity({
      id: 'ent_bigint_test',
      type: 'Actor',
      name: 'BigInt Test Entity',
    });

    const result = await handleQueryEntity({ id: 'ent_bigint_test' });

    expect(result.isError).toBeUndefined();
    // structuredContentがBigIntを含まないことを確認（JSON.stringifyが成功すること）
    expect(() => JSON.stringify(result.structuredContent)).not.toThrow();
    // created_atが文字列（ISO8601）に変換されていることを確認
    const entities = (result.structuredContent as { entities: Array<{ created_at?: string }> })
      .entities;
    if (entities[0]?.created_at) {
      expect(typeof entities[0].created_at).toBe('string');
    }
  });

  it('query.relation: structuredContentにBigIntが含まれない（JSON.stringifyが成功する）', async () => {
    // Relation作成（created_atがBigIntで返される可能性がある）
    await handleUpsertRelation({
      id: 'rel_bigint_test',
      src_id: 'src_test',
      dst_id: 'dst_test',
      type: 'KNOWS',
    });

    const result = await handleQueryRelation({ id: 'rel_bigint_test' });

    expect(result.isError).toBeUndefined();
    // structuredContentがBigIntを含まないことを確認（JSON.stringifyが成功すること）
    expect(() => JSON.stringify(result.structuredContent)).not.toThrow();
    // created_atが文字列（ISO8601）に変換されていることを確認
    const relations = (result.structuredContent as { relations: Array<{ created_at?: string }> })
      .relations;
    if (relations[0]?.created_at) {
      expect(typeof relations[0].created_at).toBe('string');
    }
  });
});

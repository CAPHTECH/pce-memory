/**
 * store/relations.ts の追加テスト
 * listRelationsByFilter, parseRelationProps のカバレッジ
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertEntity } from '../src/store/entities';
import {
  upsertRelation,
  getRelationsFromEntity,
  getRelationsToEntity,
  listAllRelations,
  listRelationsByFilter,
} from '../src/store/relations';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();

  // Create test entities
  await upsertEntity({ id: 'ent_src', type: 'Artifact', name: 'Source' });
  await upsertEntity({ id: 'ent_dst', type: 'Concept', name: 'Destination' });
});

describe('upsertRelation', () => {
  it('inserts a new relation', async () => {
    const result = await upsertRelation({
      id: 'rel_1',
      src_id: 'ent_src',
      dst_id: 'ent_dst',
      type: 'USES',
    });
    expect(result.id).toBe('rel_1');
    expect(result.type).toBe('USES');
    expect(result.src_id).toBe('ent_src');
    expect(result.dst_id).toBe('ent_dst');
  });

  it('returns existing for duplicate id (idempotent)', async () => {
    await upsertRelation({ id: 'rel_dup', src_id: 'ent_src', dst_id: 'ent_dst', type: 'USES' });
    const result = await upsertRelation({
      id: 'rel_dup',
      src_id: 'ent_src',
      dst_id: 'ent_dst',
      type: 'USES',
    });
    expect(result.id).toBe('rel_dup');
  });

  it('stores props as JSON', async () => {
    const result = await upsertRelation({
      id: 'rel_props',
      src_id: 'ent_src',
      dst_id: 'ent_dst',
      type: 'DEPENDS_ON',
      props: { version: '1.0', optional: true },
    });
    expect(result.props).toEqual({ version: '1.0', optional: true });
  });

  it('stores evidence_claim_id', async () => {
    const result = await upsertRelation({
      id: 'rel_ev',
      src_id: 'ent_src',
      dst_id: 'ent_dst',
      type: 'IMPLEMENTS',
      evidence_claim_id: 'clm_test',
    });
    expect(result.evidence_claim_id).toBe('clm_test');
  });
});

describe('getRelationsFromEntity', () => {
  it('returns empty array when no relations exist', async () => {
    const result = await getRelationsFromEntity('ent_src');
    expect(result).toEqual([]);
  });

  it('returns outgoing relations', async () => {
    await upsertRelation({ id: 'rel_out', src_id: 'ent_src', dst_id: 'ent_dst', type: 'USES' });
    const result = await getRelationsFromEntity('ent_src');
    expect(result).toHaveLength(1);
    expect(result[0]!.type).toBe('USES');
  });
});

describe('getRelationsToEntity', () => {
  it('returns incoming relations', async () => {
    await upsertRelation({ id: 'rel_in', src_id: 'ent_src', dst_id: 'ent_dst', type: 'USES' });
    const result = await getRelationsToEntity('ent_dst');
    expect(result).toHaveLength(1);
    expect(result[0]!.src_id).toBe('ent_src');
  });
});

describe('listAllRelations', () => {
  it('returns empty array when no relations', async () => {
    const result = await listAllRelations();
    expect(result).toEqual([]);
  });

  it('returns all relations', async () => {
    await upsertRelation({ id: 'rel_a', src_id: 'ent_src', dst_id: 'ent_dst', type: 'A' });
    await upsertRelation({ id: 'rel_b', src_id: 'ent_dst', dst_id: 'ent_src', type: 'B' });
    const result = await listAllRelations();
    expect(result).toHaveLength(2);
  });

  it('respects limit', async () => {
    for (let i = 0; i < 5; i++) {
      await upsertRelation({
        id: `rel_lim${i}`,
        src_id: 'ent_src',
        dst_id: 'ent_dst',
        type: `T${i}`,
      });
    }
    const result = await listAllRelations(2);
    expect(result).toHaveLength(2);
  });
});

describe('listRelationsByFilter', () => {
  it('returns all relations without filters', async () => {
    await upsertRelation({ id: 'rel_nf', src_id: 'ent_src', dst_id: 'ent_dst', type: 'X' });
    const result = await listRelationsByFilter();
    expect(result).toHaveLength(1);
  });

  it('filters by since date', async () => {
    await upsertRelation({ id: 'rel_sd', src_id: 'ent_src', dst_id: 'ent_dst', type: 'Y' });
    const futureDate = new Date(Date.now() + 86400000);
    const result = await listRelationsByFilter({ since: futureDate });
    expect(result).toEqual([]);
  });

  it('respects limit in filter', async () => {
    for (let i = 0; i < 5; i++) {
      await upsertRelation({
        id: `rel_lf${i}`,
        src_id: 'ent_src',
        dst_id: 'ent_dst',
        type: `LF${i}`,
      });
    }
    const result = await listRelationsByFilter({ limit: 3 });
    expect(result).toHaveLength(3);
  });
});

/**
 * store/entities.ts の追加テスト
 * findEntityByCanonicalKey, findEntityByName, findEntityById, listAllEntities, listEntitiesByFilter のカバレッジ
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import {
  upsertEntity,
  findEntityByCanonicalKey,
  findEntityByName,
  findEntityById,
  listAllEntities,
  listEntitiesByFilter,
} from '../src/store/entities';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('findEntityByCanonicalKey', () => {
  it('returns undefined for non-existent key', async () => {
    const result = await findEntityByCanonicalKey('nonexistent');
    expect(result).toBeUndefined();
  });

  it('finds entity by canonical_key', async () => {
    await upsertEntity({
      id: 'ent_ck1',
      type: 'Artifact',
      name: 'fp-ts',
      canonical_key: 'fp-ts',
    });

    const result = await findEntityByCanonicalKey('fp-ts');
    expect(result).toBeDefined();
    expect(result!.id).toBe('ent_ck1');
    expect(result!.name).toBe('fp-ts');
  });
});

describe('findEntityByName', () => {
  it('returns undefined for non-existent name', async () => {
    const result = await findEntityByName('nonexistent');
    expect(result).toBeUndefined();
  });

  it('finds entity by name (case-insensitive)', async () => {
    await upsertEntity({
      id: 'ent_fn1',
      type: 'Concept',
      name: 'DuckDB',
    });

    const result = await findEntityByName('duckdb');
    expect(result).toBeDefined();
    expect(result!.id).toBe('ent_fn1');
  });
});

describe('findEntityById', () => {
  it('returns undefined for non-existent id', async () => {
    const result = await findEntityById('ent_nonexistent');
    expect(result).toBeUndefined();
  });

  it('finds entity by id', async () => {
    await upsertEntity({
      id: 'ent_fi1',
      type: 'Actor',
      name: 'Claude',
    });

    const result = await findEntityById('ent_fi1');
    expect(result).toBeDefined();
    expect(result!.name).toBe('Claude');
    expect(result!.type).toBe('Actor');
  });
});

describe('listAllEntities', () => {
  it('returns empty array when no entities exist', async () => {
    const result = await listAllEntities();
    expect(result).toEqual([]);
  });

  it('returns all entities', async () => {
    await upsertEntity({ id: 'ent_la1', type: 'Artifact', name: 'A' });
    await upsertEntity({ id: 'ent_la2', type: 'Concept', name: 'B' });

    const result = await listAllEntities();
    expect(result).toHaveLength(2);
  });

  it('respects limit parameter', async () => {
    for (let i = 0; i < 5; i++) {
      await upsertEntity({ id: `ent_lim${i}`, type: 'Event', name: `Event ${i}` });
    }
    const result = await listAllEntities(2);
    expect(result).toHaveLength(2);
  });
});

describe('listEntitiesByFilter', () => {
  it('returns all entities without filters', async () => {
    await upsertEntity({ id: 'ent_f1', type: 'Artifact', name: 'X' });
    const result = await listEntitiesByFilter();
    expect(result).toHaveLength(1);
  });

  it('filters by since date', async () => {
    await upsertEntity({ id: 'ent_f2', type: 'Actor', name: 'Y' });
    // Filter with future date should return nothing
    const futureDate = new Date(Date.now() + 86400000);
    const result = await listEntitiesByFilter({ since: futureDate });
    expect(result).toEqual([]);
  });

  it('respects limit in filter', async () => {
    for (let i = 0; i < 5; i++) {
      await upsertEntity({ id: `ent_fl${i}`, type: 'Concept', name: `C${i}` });
    }
    const result = await listEntitiesByFilter({ limit: 3 });
    expect(result).toHaveLength(3);
  });
});

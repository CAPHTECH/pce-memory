/**
 * store/claimsEither.ts のテスト
 * Either版Claims CRUD操作のカバレッジ
 */
import { describe, it, expect, beforeEach } from 'vitest';
import * as E from 'fp-ts/Either';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState } from '../src/store/rate';
import {
  findClaimByIdE,
  findClaimByHashE,
  upsertClaimE,
  listClaimsByScopeE,
  claimExistsE,
} from '../src/store/claimsEither';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
});

const makeClaim = (overrides?: Partial<{ text: string; kind: string; scope: string; content_hash: string }>) => ({
  text: 'test claim text',
  kind: 'fact',
  scope: 'project',
  boundary_class: 'internal',
  content_hash: `sha256:${'a'.repeat(64)}`,
  ...overrides,
});

describe('upsertClaimE', () => {
  it('inserts new claim and returns it', async () => {
    const result = await upsertClaimE(makeClaim())();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.id).toMatch(/^clm_/);
      expect(result.right.text).toBe('test claim text');
      expect(result.right.kind).toBe('fact');
      expect(result.right.scope).toBe('project');
      expect(result.right.boundary_class).toBe('internal');
    }
  });

  it('returns existing claim for duplicate content_hash (idempotent)', async () => {
    const first = await upsertClaimE(makeClaim())();
    const second = await upsertClaimE(makeClaim())();

    expect(E.isRight(first)).toBe(true);
    expect(E.isRight(second)).toBe(true);
    if (E.isRight(first) && E.isRight(second)) {
      expect(first.right.id).toBe(second.right.id);
    }
  });

  it('sets default status to active', async () => {
    const result = await upsertClaimE(makeClaim())();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.status).toBe('active');
    }
  });

  it('accepts memory_type', async () => {
    const result = await upsertClaimE({
      ...makeClaim({ content_hash: `sha256:${'b'.repeat(64)}` }),
      memory_type: 'knowledge',
    })();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.memory_type).toBe('knowledge');
    }
  });
});

describe('findClaimByIdE', () => {
  it('returns undefined for non-existent id', async () => {
    const result = await findClaimByIdE('clm_nonexistent')();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it('finds claim by id after upsert', async () => {
    const upsertResult = await upsertClaimE(makeClaim())();
    expect(E.isRight(upsertResult)).toBe(true);
    if (!E.isRight(upsertResult)) return;

    const findResult = await findClaimByIdE(upsertResult.right.id)();
    expect(E.isRight(findResult)).toBe(true);
    if (E.isRight(findResult)) {
      expect(findResult.right).toBeDefined();
      expect(findResult.right!.text).toBe('test claim text');
    }
  });
});

describe('findClaimByHashE', () => {
  it('returns undefined for non-existent hash', async () => {
    const result = await findClaimByHashE(`sha256:${'f'.repeat(64)}`)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it('finds claim by content_hash', async () => {
    const hash = `sha256:${'c'.repeat(64)}`;
    await upsertClaimE(makeClaim({ content_hash: hash }))();

    const result = await findClaimByHashE(hash)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeDefined();
      expect(result.right!.content_hash).toBe(hash);
    }
  });
});

describe('listClaimsByScopeE', () => {
  it('returns empty array when no claims exist', async () => {
    const result = await listClaimsByScopeE(['project'], 10)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual([]);
    }
  });

  it('lists claims filtered by scope', async () => {
    await upsertClaimE(makeClaim({ content_hash: `sha256:${'1'.repeat(64)}`, scope: 'project' }))();
    await upsertClaimE(makeClaim({ content_hash: `sha256:${'2'.repeat(64)}`, scope: 'principle' }))();

    const projectOnly = await listClaimsByScopeE(['project'], 10)();
    expect(E.isRight(projectOnly)).toBe(true);
    if (E.isRight(projectOnly)) {
      expect(projectOnly.right).toHaveLength(1);
      expect(projectOnly.right[0]!.scope).toBe('project');
    }
  });

  it('filters by query text', async () => {
    await upsertClaimE(makeClaim({ text: 'JWT authentication', content_hash: `sha256:${'3'.repeat(64)}` }))();
    await upsertClaimE(makeClaim({ text: 'DuckDB storage', content_hash: `sha256:${'4'.repeat(64)}` }))();

    const result = await listClaimsByScopeE(['project'], 10, 'JWT')();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toHaveLength(1);
      expect(result.right[0]!.text).toContain('JWT');
    }
  });

  it('respects limit parameter', async () => {
    for (let i = 0; i < 5; i++) {
      await upsertClaimE(makeClaim({ text: `claim ${i}`, content_hash: `sha256:${String(i).repeat(64)}` }))();
    }

    const result = await listClaimsByScopeE(['project'], 2)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.length).toBeLessThanOrEqual(2);
    }
  });

  it('handles multiple scopes', async () => {
    await upsertClaimE(makeClaim({ scope: 'project', content_hash: `sha256:${'5'.repeat(64)}` }))();
    await upsertClaimE(makeClaim({ scope: 'principle', content_hash: `sha256:${'6'.repeat(64)}` }))();

    const result = await listClaimsByScopeE(['project', 'principle'], 10)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toHaveLength(2);
    }
  });
});

describe('claimExistsE', () => {
  it('returns false for non-existent claim', async () => {
    const result = await claimExistsE('clm_nonexistent')();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe(false);
    }
  });

  it('returns true for existing claim', async () => {
    const upsertResult = await upsertClaimE(makeClaim())();
    expect(E.isRight(upsertResult)).toBe(true);
    if (!E.isRight(upsertResult)) return;

    const existsResult = await claimExistsE(upsertResult.right.id)();
    expect(E.isRight(existsResult)).toBe(true);
    if (E.isRight(existsResult)) {
      expect(existsResult.right).toBe(true);
    }
  });
});

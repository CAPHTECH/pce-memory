import { describe, it, expect, beforeEach } from 'vitest';
import { ContentHashCollisionError, upsertClaim } from '../src/store/claims';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('upsertClaim', () => {
  it('returns same id on duplicate content_hash for identical text', async () => {
    const { claim: first, isNew: isFirstNew } = await upsertClaim({
      text: 'foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'hash123',
    });
    expect(isFirstNew).toBe(true);

    const { claim: second, isNew: isSecondNew } = await upsertClaim({
      text: 'foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'hash123',
    });
    expect(isSecondNew).toBe(false);
    expect(second.id).toBe(first.id);
  });

  it('rejects duplicate content_hash when the text differs', async () => {
    await upsertClaim({
      text: 'foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'hash123',
    });

    await expect(
      upsertClaim({
        text: 'foo2',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'hash123',
      })
    ).rejects.toBeInstanceOf(ContentHashCollisionError);
  });
});

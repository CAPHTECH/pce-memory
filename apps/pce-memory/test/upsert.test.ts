import { describe, it, expect, beforeEach } from 'vitest';
import { ContentHashCollisionError, markClaimRolledBack, upsertClaim } from '../src/store/claims';
import { isDomainError } from '../src/domain/errors';
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
    ).rejects.toSatisfy(
      (e: unknown) =>
        e instanceof ContentHashCollisionError &&
        isDomainError(e) &&
        e.code === 'CONTENT_HASH_COLLISION'
    );
  });

  it('rejects revived tombstoned claims when the text collides', async () => {
    const original = await upsertClaim({
      text: 'tombstoned foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'hash-rolled-back-001',
    });
    await markClaimRolledBack(original.claim.id, {
      tombstone_at: '2025-01-01T00:00:00.000Z',
      rollback_reason: 'test rollback',
      superseded_by: 'rbk_test_001',
    });

    await expect(
      upsertClaim({
        text: 'tombstoned foo v2',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'hash-rolled-back-001',
      })
    ).rejects.toSatisfy(
      (e: unknown) =>
        e instanceof ContentHashCollisionError &&
        isDomainError(e) &&
        e.code === 'CONTENT_HASH_COLLISION'
    );
  });
});

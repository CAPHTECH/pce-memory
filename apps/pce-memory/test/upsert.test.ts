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

  it('revives rolled-back claims without overwriting their classification metadata', async () => {
    const original = await upsertClaim({
      text: 'stable revived claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
      content_hash: 'hash-rolled-back-002',
    });

    await markClaimRolledBack(original.claim.id, {
      tombstone_at: '2025-01-01T00:00:00.000Z',
      rollback_reason: 'test rollback',
      superseded_by: 'rbk_test_002',
    });

    const revived = await upsertClaim({
      text: 'stable revived claim',
      kind: 'task',
      scope: 'principle',
      boundary_class: 'public',
      memory_type: 'norm',
      provenance: { at: '2025-01-02T00:00:00.000Z', actor: 'vitest-2' },
      content_hash: 'hash-rolled-back-002',
    });

    expect(revived.claim.id).toBe(original.claim.id);
    expect(revived.claim.kind).toBe('fact');
    expect(revived.claim.scope).toBe('project');
    expect(revived.claim.boundary_class).toBe('internal');
    expect(revived.claim.memory_type).toBe('knowledge');
    expect(revived.claim.provenance).toEqual(
      expect.objectContaining({ actor: 'vitest', at: '2025-01-01T00:00:00.000Z' })
    );
  });
});

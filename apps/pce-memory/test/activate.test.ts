import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim, listClaimsByScope } from '../src/store/claims';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('activate validation', () => {
  it('returns validation error when scope is unknown', async () => {
    const scopes = await listClaimsByScope(['unknown'], 10);
    expect(scopes.length).toBe(0);
  });

  it('filters claims by scope', async () => {
    await upsertClaim({
      text: 'a',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'h1',
    });
    await upsertClaim({
      text: 'b',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'h2',
    });
    const scopes = await listClaimsByScope(['project'], 10);
    expect(scopes.map((c) => c.scope)).toEqual(['project']);
  });
});

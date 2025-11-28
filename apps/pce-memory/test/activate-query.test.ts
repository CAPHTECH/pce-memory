import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim, listClaimsByScope } from '../src/store/claims';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('activate query filtering', () => {
  it('filters by scope and q substring', async () => {
    await upsertClaim({
      text: 'foo alpha',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'q1',
    });
    await upsertClaim({
      text: 'beta',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'q2',
    });
    const res = await listClaimsByScope(['project'], 10, 'alpha');
    expect(res.map((c) => c.text)).toEqual(['foo alpha']);
  });
});

import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim, listClaimsByScope } from '../src/store/claims';
import { boundaryValidate } from '@pce/boundary';
import { defaultPolicy } from '@pce/policy-schemas/src/defaults';
import { recordFeedback } from '../src/store/feedback';
import { updateCritic } from '../src/store/critic';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('E2E happy path (upsert->activate->validate->feedback)', () => {
  it('runs end-to-end without errors', async () => {
    // upsert
    const { claim, isNew } = await upsertClaim({
      text: 'foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'e2e1',
    });
    expect(claim.id).toBeDefined();
    expect(isNew).toBe(true);

    // activate
    const claims = await listClaimsByScope(['project'], 10);
    expect(claims.length).toBe(1);

    // boundary.validate - verifies that validation passes for project scope
    // Note: public class with allow: ["*"] always matches first, so no redaction happens
    const val = boundaryValidate(
      { payload: 'test payload', allow: ['answer:task'], scope: 'project' },
      defaultPolicy.boundary
    );
    expect(val.allowed).toBe(true);
    expect(val.redacted).toBeDefined();

    // feedback + critic
    await recordFeedback({ claim_id: claim.id, signal: 'helpful', score: 1 });
    const next = await updateCritic(claim.id, 1, 0, 5);
    expect(next).toBeGreaterThan(0);
  });
});

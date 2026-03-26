import { beforeEach, describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash } from '@pce/embeddings';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import { saveActiveContext, saveActiveContextItems } from '../src/store/activeContext';
import { upsertClaimLink } from '../src/store/claimLinks';
import { collectRollbackTopologyBlastRadius } from '../src/store/rollbackTopology';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

async function createClaim(text: string): Promise<string> {
  const { claim } = await upsertClaim({
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
  });
  return claim.id;
}

async function saveSingleClaimContext(activeContextId: string, claimId: string): Promise<void> {
  await saveActiveContext({
    id: activeContextId,
    claims: [{ id: claimId } as { id: string }],
    intent: 'resume_task',
    policy_version: 'policy-test',
  });
  await saveActiveContextItems([
    {
      id: `aci_${activeContextId}`,
      active_context_id: activeContextId,
      claim_id: claimId,
      source_layer: 'meso',
      score: 1,
      selection_reason: activeContextId,
      rank: 1,
    },
  ]);
}

describe('Property: rollback topology invariants', () => {
  it('Property: affected_active_contexts includes impacted claims and excludes unrelated ones', async () => {
    await fc.assert(
      fc.asyncProperty(fc.integer({ min: 0, max: 4 }), async (unrelatedCount) => {
        await resetDbAsync();
        process.env.PCE_DB = ':memory:';
        await initDb();
        await initSchema();

        const rootId = await createClaim('rollback-root');
        const supportId = await createClaim('rollback-support');
        await upsertClaimLink({
          source_claim_id: supportId,
          target_claim_id: rootId,
          link_type: 'supports',
        });

        await saveSingleClaimContext('ac_root', rootId);
        await saveSingleClaimContext('ac_support', supportId);

        const unrelatedContextIds: string[] = [];
        for (let index = 0; index < unrelatedCount; index++) {
          const unrelatedId = await createClaim(`rollback-unrelated-${index}`);
          const contextId = `ac_unrelated_${index}`;
          unrelatedContextIds.push(contextId);
          await saveSingleClaimContext(contextId, unrelatedId);
        }

        const blastRadius = await collectRollbackTopologyBlastRadius(rootId);
        const affectedIds = blastRadius.affected_active_contexts.map((item) => item.active_context_id);

        expect(affectedIds).toEqual(expect.arrayContaining(['ac_root', 'ac_support']));
        for (const contextId of unrelatedContextIds) {
          expect(affectedIds).not.toContain(contextId);
        }
      }),
      { numRuns: 12 }
    );
  });
});

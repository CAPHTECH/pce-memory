import { afterEach, describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash } from '@pce/embeddings';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import { linkClaimEntity, upsertEntity } from '../src/store/entities';
import { auditGraph } from '../src/store/graphAudit';

afterEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
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

describe('Property: graph audit invariants', () => {
  it('Property: claim-to-entity attachments alone should prevent orphan_claim findings', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(fc.string({ minLength: 1, maxLength: 20 }), {
          minLength: 1,
          maxLength: 5,
        }),
        async (labels) => {
          const normalized = [...new Set(labels.map((label, index) => `${label}-${index}`))];
          if (normalized.length === 0) {
            return;
          }

          await resetDbAsync();
          process.env.PCE_DB = ':memory:';
          await initDb();
          await initSchema();

          const claimIds: string[] = [];
          for (const [index, label] of normalized.entries()) {
            const claimId = await createClaim(`entity-attached claim ${label}`);
            claimIds.push(claimId);
            await upsertEntity({
              id: `ent_attached_${index}`,
              type: 'Concept',
              name: `Entity ${label}`,
            });
            await linkClaimEntity(claimId, `ent_attached_${index}`);
          }

          const report = await auditGraph();
          const orphanClaimIds = report.findings
            .filter((finding) => finding.kind === 'orphan_claim')
            .flatMap((finding) => finding.node_ids ?? []);

          for (const claimId of claimIds) {
            expect(orphanClaimIds).not.toContain(claimId);
          }
        }
      ),
      { numRuns: 20 }
    );
  });

  it('Property: max_findings_per_kind limits findings per kind', async () => {
    await fc.assert(
      fc.asyncProperty(fc.integer({ min: 1, max: 3 }), async (threshold) => {
        await resetDbAsync();
        process.env.PCE_DB = ':memory:';
        await initDb();
        await initSchema();

        const claimCount = threshold + 3;
        for (let index = 0; index < claimCount; index++) {
          await createClaim(`orphan claim ${threshold}-${index}`);
        }

        const report = await auditGraph({ maxFindingsPerKind: threshold });
        const countsByKind = report.findings.reduce<Record<string, number>>((acc, finding) => {
          acc[finding.kind] = (acc[finding.kind] ?? 0) + 1;
          return acc;
        }, {});

        for (const count of Object.values(countsByKind)) {
          expect(count).toBeLessThanOrEqual(threshold);
        }
      }),
      { numRuns: 10 }
    );
  });
});

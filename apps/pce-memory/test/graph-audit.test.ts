import { afterEach, beforeEach, describe, expect, it, vi } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState, resetRates } from '../src/store/rate';
import { upsertClaim } from '../src/store/claims';
import { upsertEntity, linkClaimEntity } from '../src/store/entities';
import { upsertRelation } from '../src/store/relations';
import { upsertClaimLink } from '../src/store/claimLinks';
import { saveActiveContextItems } from '../src/store/activeContext';
import * as graphAuditStore from '../src/store/graphAudit';
import * as logsStore from '../src/store/logs';
import { handleGraphAudit } from '../src/core/handlers/graphAudit';

async function createClaim(text: string, scope: 'project' | 'principle' | 'session' = 'project') {
  return (
    await upsertClaim({
      text,
      kind: 'fact',
      scope,
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    })
  ).claim;
}

async function seedCoactivationPair(
  contextId: string,
  leftClaimId: string,
  rightClaimId: string
): Promise<void> {
  await saveActiveContextItems([
    {
      id: `aci_${contextId}_1`,
      active_context_id: contextId,
      claim_id: leftClaimId,
      source_layer: 'meso',
      score: 1,
      rank: 1,
    },
    {
      id: `aci_${contextId}_2`,
      active_context_id: contextId,
      claim_id: rightClaimId,
      source_layer: 'meso',
      score: 0.9,
      rank: 2,
    },
  ]);
}

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

afterEach(() => {
  vi.restoreAllMocks();
});

describe('auditGraph', () => {
  it('detects orphan nodes, cycles, supersession chains, scope holes, coactivation gaps, and generic hubs', async () => {
    const orphanClaim = await createClaim('Orphan claim text');
    await upsertEntity({ id: 'ent_orphan', type: 'Concept', name: 'Unused Entity' });

    const cycleA = await createClaim('Cycle A text');
    const cycleB = await createClaim('Cycle B text');
    const cycleC = await createClaim('Cycle C text');
    await upsertClaimLink({
      source_claim_id: cycleA.id,
      target_claim_id: cycleB.id,
      link_type: 'contradicts',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });
    await upsertClaimLink({
      source_claim_id: cycleB.id,
      target_claim_id: cycleC.id,
      link_type: 'contradicts',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });
    await upsertClaimLink({
      source_claim_id: cycleC.id,
      target_claim_id: cycleA.id,
      link_type: 'contradicts',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });

    const superA = await createClaim('Supersession A text');
    const superB = await createClaim('Supersession B text');
    const superC = await createClaim('Supersession C text');
    const superD = await createClaim('Supersession D text');
    await upsertClaimLink({
      source_claim_id: superA.id,
      target_claim_id: superB.id,
      link_type: 'supersedes',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });
    await upsertClaimLink({
      source_claim_id: superB.id,
      target_claim_id: superC.id,
      link_type: 'supersedes',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });
    await upsertClaimLink({
      source_claim_id: superC.id,
      target_claim_id: superD.id,
      link_type: 'supersedes',
      provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
    });

    const project1 = await createClaim('Project component alpha');
    const project2 = await createClaim('Project component beta');
    const project3 = await createClaim('Project component gamma');
    const genericEntity = await upsertEntity({
      id: 'ent_generic',
      type: 'Concept',
      name: 'General',
    });
    await linkClaimEntity(project1.id, genericEntity.id);
    await linkClaimEntity(project2.id, genericEntity.id);
    await linkClaimEntity(project3.id, genericEntity.id);

    const relationEntity = await upsertEntity({
      id: 'ent_relation',
      type: 'Artifact',
      name: 'Relation Anchor',
    });
    const relationClaim = await createClaim('Relation attached claim');
    await linkClaimEntity(relationClaim.id, relationEntity.id);
    await upsertRelation({
      id: 'rel_bridge',
      src_id: genericEntity.id,
      dst_id: relationEntity.id,
      type: 'ASSOCIATED_WITH',
    });

    const coactiveLeft = await createClaim('Coactive left claim');
    const coactiveRight = await createClaim('Coactive right claim');
    await seedCoactivationPair('ac_1', coactiveLeft.id, coactiveRight.id);
    await seedCoactivationPair('ac_2', coactiveLeft.id, coactiveRight.id);
    await seedCoactivationPair('ac_3', coactiveLeft.id, coactiveRight.id);

    const report = await graphAuditStore.auditGraph({
      minSupersessionChainLength: 3,
      repeatedCoactivationThreshold: 3,
      genericHubDegreeThreshold: 3,
    });

    expect(report.summary.orphan_claims).toBeGreaterThanOrEqual(1);
    expect(report.summary.orphan_entities).toBeGreaterThanOrEqual(1);
    expect(report.summary.contradiction_cycles).toBeGreaterThanOrEqual(1);
    expect(report.summary.supersession_chains).toBeGreaterThanOrEqual(1);
    expect(report.summary.scope_holes).toBeGreaterThanOrEqual(1);
    expect(report.summary.repeated_coactivations).toBeGreaterThanOrEqual(1);
    expect(report.summary.generic_hubs).toBeGreaterThanOrEqual(1);

    expect(report.findings).toEqual(
      expect.arrayContaining([
        expect.objectContaining({ kind: 'orphan_claim', node_ids: [orphanClaim.id] }),
        expect.objectContaining({ kind: 'orphan_entity', node_ids: ['ent_orphan'] }),
        expect.objectContaining({ kind: 'contradiction_cycle' }),
        expect.objectContaining({ kind: 'supersession_chain' }),
        expect.objectContaining({
          kind: 'scope_hole',
          details: expect.objectContaining({
            missing_scopes: expect.arrayContaining(['principle']),
          }),
        }),
        expect.objectContaining({
          kind: 'repeated_coactivation',
          node_ids: expect.arrayContaining([coactiveLeft.id, coactiveRight.id]),
        }),
        expect.objectContaining({
          kind: 'generic_hub',
          node_ids: [genericEntity.id],
        }),
      ])
    );
  });

  it('wraps the audit report in a tool result', async () => {
    const left = await createClaim('Handler wrapper claim left');
    const right = await createClaim('Handler wrapper claim right');
    await seedCoactivationPair('ac_wrapper_1', left.id, right.id);

    const result = await handleGraphAudit({});
    expect(result.isError).not.toBe(true);
    const payload = JSON.parse(result.content[0]!.text) as {
      summary: { claims: number };
      findings: unknown[];
      request_id: string;
      trace_id: string;
    };
    expect(payload.summary.claims).toBeGreaterThanOrEqual(1);
    expect(payload.request_id).toBeDefined();
    expect(payload.trace_id).toBeDefined();
    expect(Array.isArray(payload.findings)).toBe(true);
  });

  it('does not classify claims with entity attachments as orphan_claim', async () => {
    const claim = await createClaim('Entity-attached claim without claim-link peers');
    await upsertEntity({ id: 'ent_attached_only', type: 'Concept', name: 'Attached Only' });
    await linkClaimEntity(claim.id, 'ent_attached_only');

    const report = await graphAuditStore.auditGraph();
    expect(report.findings).not.toEqual(
      expect.arrayContaining([
        expect.objectContaining({ kind: 'orphan_claim', node_ids: [claim.id] }),
      ])
    );
  });

  it('applies maxFindingsPerKind to each finding kind independently', async () => {
    for (let index = 0; index < 4; index++) {
      await createClaim(`Orphan capped claim ${index}`);
    }

    const report = await graphAuditStore.auditGraph({ maxFindingsPerKind: 1 });
    const orphanFindings = report.findings.filter((finding) => finding.kind === 'orphan_claim');

    expect(orphanFindings).toHaveLength(1);
  });

  it('signals truncation when the scan limit is exceeded', async () => {
    await createClaim('Truncated claim 1');
    await createClaim('Truncated claim 2');

    const report = await graphAuditStore.auditGraph({ scanLimit: 1 });

    expect(report.truncation).toEqual(
      expect.objectContaining({
        claims: true,
        entities: false,
        relations: false,
      })
    );
    expect(report.summary.truncated).toBe(true);
    expect(report.summary.claims).toBe(1);
  });

  it('returns the audit report even when success logging fails', async () => {
    vi.spyOn(logsStore, 'appendLog').mockRejectedValueOnce(new Error('log write failed'));

    const result = await handleGraphAudit({});
    expect(result.isError).not.toBe(true);

    const payload = result.structuredContent as {
      summary: { claims: number };
      request_id: string;
      trace_id: string;
    };
    expect(payload.summary.claims).toBeGreaterThanOrEqual(0);
    expect(payload.request_id).toBeDefined();
    expect(payload.trace_id).toBeDefined();
  });

  it('preserves the original DB error when failure logging also fails', async () => {
    vi.spyOn(graphAuditStore, 'auditGraph').mockRejectedValueOnce(new Error('audit exploded'));
    vi.spyOn(logsStore, 'appendLog').mockRejectedValueOnce(new Error('log write failed'));

    const result = await handleGraphAudit({});
    expect(result.isError).toBe(true);
    expect(result.structuredContent).toEqual(
      expect.objectContaining({
        error: expect.objectContaining({
          code: 'DB_ERROR',
          message: 'audit exploded',
        }),
      })
    );
  });
});

import { beforeEach, describe, expect, it } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import { upsertEntity, linkClaimEntity } from '../src/store/entities';
import { upsertClaimLink } from '../src/store/claimLinks';
import { upsertRelation } from '../src/store/relations';
import { saveActiveContext, saveActiveContextItems } from '../src/store/activeContext';
import { collectRollbackTopologyBlastRadius } from '../src/store/rollbackTopology';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

async function createClaim(
  text: string,
  contentHash: string
): Promise<Awaited<ReturnType<typeof upsertClaim>>['claim']> {
  const { claim } = await upsertClaim({
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: contentHash,
  });
  return claim;
}

describe('collectRollbackTopologyBlastRadius', () => {
  it('collects connected claims, linked entities, active contexts, and topology neighborhoods', async () => {
    const root = await createClaim('root topology claim', 'sha256:rollback-root');
    const support = await createClaim('supporting topology claim', 'sha256:rollback-support');
    const conflict = await createClaim('conflicting topology claim', 'sha256:rollback-conflict');
    const superseded = await createClaim('superseded topology claim', 'sha256:rollback-old');
    const entityClaim = await createClaim('entity-connected topology claim', 'sha256:rollback-entity');
    const unrelated = await createClaim('unrelated claim', 'sha256:rollback-unrelated');

    await upsertEntity({ id: 'ent_root', type: 'Artifact', name: 'Root Entity' });
    await upsertEntity({ id: 'ent_support', type: 'Concept', name: 'Support Entity' });
    await upsertEntity({ id: 'ent_conflict', type: 'Concept', name: 'Conflict Entity' });
    await upsertEntity({ id: 'ent_superseded', type: 'Concept', name: 'Old Entity' });
    await upsertEntity({ id: 'ent_entity', type: 'Artifact', name: 'Bridge Entity' });
    await upsertEntity({ id: 'ent_unrelated', type: 'Concept', name: 'Unrelated Entity' });

    await linkClaimEntity(root.id, 'ent_root');
    await linkClaimEntity(support.id, 'ent_support');
    await linkClaimEntity(conflict.id, 'ent_conflict');
    await linkClaimEntity(superseded.id, 'ent_superseded');
    await linkClaimEntity(entityClaim.id, 'ent_entity');
    await linkClaimEntity(unrelated.id, 'ent_unrelated');

    await upsertClaimLink({
      source_claim_id: support.id,
      target_claim_id: root.id,
      link_type: 'supports',
      confidence: 0.95,
    });
    await upsertClaimLink({
      source_claim_id: conflict.id,
      target_claim_id: root.id,
      link_type: 'contradicts',
      confidence: 0.85,
    });
    await upsertClaimLink({
      source_claim_id: superseded.id,
      target_claim_id: root.id,
      link_type: 'supersedes',
      confidence: 0.9,
    });

    await upsertRelation({
      id: 'rel_bridge',
      src_id: 'ent_root',
      dst_id: 'ent_entity',
      type: 'DEPENDS_ON',
      evidence_claim_id: root.id,
    });

    await upsertRelation({
      id: 'rel_bridge_2',
      src_id: 'ent_entity',
      dst_id: 'ent_root',
      type: 'RELATES_TO',
      evidence_claim_id: entityClaim.id,
    });

    await upsertRelation({
      id: 'rel_bridge_3',
      src_id: 'ent_root',
      dst_id: 'ent_conflict',
      type: 'RELATES_TO',
      evidence_claim_id: conflict.id,
    });

    await upsertRelation({
      id: 'rel_bridge_4',
      src_id: 'ent_root',
      dst_id: 'ent_superseded',
      type: 'RELATES_TO',
      evidence_claim_id: superseded.id,
    });

    await expect(
      saveActiveContext({
        id: 'ac_rollback_1',
        claims: [root, support, entityClaim],
        intent: 'resume_task',
        policy_version: 'policy-test',
      })
    ).resolves.toBeUndefined();
    await expect(
      saveActiveContextItems([
        {
          id: 'aci_root',
          active_context_id: 'ac_rollback_1',
          claim_id: root.id,
          source_layer: 'meso',
          score: 0.99,
          selection_reason: 'root',
          rank: 1,
        },
        {
          id: 'aci_support',
          active_context_id: 'ac_rollback_1',
          claim_id: support.id,
          source_layer: 'meso',
          score: 0.88,
          selection_reason: 'support',
          rank: 2,
        },
        {
          id: 'aci_entity',
          active_context_id: 'ac_rollback_1',
          claim_id: entityClaim.id,
          source_layer: 'meso',
          score: 0.77,
          selection_reason: 'entity',
          rank: 3,
        },
      ])
    ).resolves.toBeUndefined();

    await expect(
      saveActiveContext({
        id: 'ac_rollback_2',
        claims: [conflict, superseded],
        intent: 'resume_task',
        policy_version: 'policy-test',
      })
    ).resolves.toBeUndefined();
    await expect(
      saveActiveContextItems([
        {
          id: 'aci_conflict',
          active_context_id: 'ac_rollback_2',
          claim_id: conflict.id,
          source_layer: 'meso',
          score: 0.66,
          selection_reason: 'conflict',
          rank: 1,
        },
        {
          id: 'aci_superseded',
          active_context_id: 'ac_rollback_2',
          claim_id: superseded.id,
          source_layer: 'meso',
          score: 0.55,
          selection_reason: 'superseded',
          rank: 2,
        },
      ])
    ).resolves.toBeUndefined();

    await saveActiveContext({
      id: 'ac_rollback_3',
      claims: [unrelated],
      intent: 'resume_task',
      policy_version: 'policy-test',
    });
    await saveActiveContextItems([
      {
        id: 'aci_unrelated',
        active_context_id: 'ac_rollback_3',
        claim_id: unrelated.id,
        source_layer: 'meso',
        score: 0.44,
        selection_reason: 'unrelated',
        rank: 1,
      },
    ]);

    const result = await collectRollbackTopologyBlastRadius(root.id);

    expect(result.root_claim.id).toBe(root.id);
    expect(result.target_layer).toBe('meso');
    expect(result.connected_claims.map((item) => item.claim.id)).toEqual(
      expect.arrayContaining([support.id, conflict.id, superseded.id, entityClaim.id])
    );
    expect(result.connected_claims.some((item) => item.claim.id === root.id)).toBe(false);

    expect(result.neighborhoods.support.map((item) => item.claim.id)).toEqual(
      expect.arrayContaining([support.id, conflict.id, superseded.id, entityClaim.id])
    );
    expect(result.neighborhoods.conflict.map((item) => item.claim.id)).toContain(conflict.id);
    expect(result.neighborhoods.supersession.map((item) => item.claim.id)).toContain(superseded.id);

    expect(result.linked_entities.map((item) => item.entity.id)).toEqual(
      expect.arrayContaining(['ent_root', 'ent_support', 'ent_conflict', 'ent_superseded', 'ent_entity'])
    );

    expect(result.affected_active_contexts.map((item) => item.active_context_id)).toEqual(
      expect.arrayContaining(['ac_rollback_1', 'ac_rollback_2'])
    );
    expect(result.affected_active_contexts.some((item) => item.active_context_id === 'ac_rollback_3')).toBe(false);

    expect(result.summary).toEqual(
      expect.objectContaining({
        connected_claims: 4,
        linked_entities: 5,
        affected_active_contexts: 2,
        support: 4,
        conflict: 1,
        supersession: 1,
      })
    );
  });

  it('throws for unknown claims', async () => {
    await expect(collectRollbackTopologyBlastRadius('clm_missing')).rejects.toThrow(
      'claim not found: clm_missing'
    );
  });
});

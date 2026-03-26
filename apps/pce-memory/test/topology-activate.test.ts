import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';
import { setEmbeddingService } from '../src/store/hybridSearch';

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createEmbeddingService(embeddings: Record<string, readonly number[]>): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      async () =>
        E.right({
          embedding: embeddings[text] ?? normalize([-1, 0]),
          modelVersion: 'topology-activate-test-v1',
        }),
  };
}

async function applyPolicy(): Promise<void> {
  await dispatchTool('pce_memory_policy_apply', {});
}

async function applyPolicyWithTopologyEnabled(enabled: boolean): Promise<void> {
  await dispatchTool('pce_memory_policy_apply', {
    yaml: `
version: '0.1'
boundary:
  version: '0.1'
  scopes:
    session: { ttl: '7d' }
    project: { ttl: '120d' }
    principle: { ttl: 'inf' }
  boundary_classes:
    public: { allow: ['*'] }
    internal: { allow: ['answer:task', 'tool:*'] }
    pii:
      allow: ['tool:contact-lookup']
      redact: ['email', 'phone']
      escalation: 'human_review'
    secret: { allow: [], escalation: 'deny' }
retrieval:
  hybrid:
    alpha: 0.65
    threshold: 0.15
    k_txt: 48
    k_vec: 96
    k_final: 12
    recency_half_life_days: 30
    topology:
      enabled: ${enabled}
maintenance:
  hints_enabled: true
  similarity_threshold: 0.9
  stale_days: 30
`.trim(),
  });
}

async function upsertKnowledge(
  text: string,
  options: {
    scope?: 'project' | 'principle' | 'session';
    boundary_class?: 'public' | 'internal' | 'pii';
  } = {}
): Promise<string> {
  const result = await dispatchTool('pce_memory_upsert', {
    text,
    kind: 'fact',
    scope: options.scope ?? 'project',
    boundary_class: options.boundary_class ?? 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
  });
  return result.structuredContent!.id as string;
}

async function resetTopologyTestState(): Promise<void> {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

beforeEach(async () => {
  await resetTopologyTestState();
});

describe('topology-aware activate', () => {
  it('follows supports forward only', async () => {
    const supportText = 'support seed alpha';
    const rootText = 'root destination beta';
    const querySupport = 'support query alpha';
    const queryRoot = 'root query beta';
    setEmbeddingService(
      createEmbeddingService({
        [supportText]: normalize([1, 0]),
        [rootText]: normalize([-1, 0]),
        [querySupport]: normalize([1, 0]),
        [queryRoot]: normalize([-1, 0]),
      })
    );
    await applyPolicy();

    const supportId = await upsertKnowledge(supportText);
    const rootId = await upsertKnowledge(rootText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: supportId,
      target_claim_id: rootId,
      link_type: 'supports',
    });

    const forward = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: querySupport,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{
        claim: { id: string };
        source?: string;
        topology?: { kind: string; path?: Array<{ link_type?: string }> };
      }>;
    };
    expect(forward.claims.map((item) => item.claim.id)).toEqual(
      expect.arrayContaining([supportId, rootId])
    );
    expect(forward.claims.find((item) => item.claim.id === rootId)).toEqual(
      expect.objectContaining({
        source: 'claim_link',
        topology: expect.objectContaining({
          kind: 'support',
          path: expect.arrayContaining([expect.objectContaining({ link_type: 'supports' })]),
        }),
      })
    );

    const reverse = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryRoot,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{ claim: { id: string } }>;
    };
    expect(reverse.claims.map((item) => item.claim.id)).toContain(rootId);
    expect(reverse.claims.map((item) => item.claim.id)).not.toContain(supportId);
  });

  it('surfaces contradicting claims as conflict context', async () => {
    const anchorText = 'anchor seed gamma';
    const conflictText = 'conflict note delta';
    const queryText = 'anchor query gamma';
    setEmbeddingService(
      createEmbeddingService({
        [anchorText]: normalize([1, 0]),
        [conflictText]: normalize([-1, 0]),
        [queryText]: normalize([1, 0]),
      })
    );
    await applyPolicy();

    const anchorId = await upsertKnowledge(anchorText);
    const conflictId = await upsertKnowledge(conflictText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: conflictId,
      target_claim_id: anchorId,
      link_type: 'contradicts',
    });

    const activate = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{
        claim: { id: string };
        source?: string;
        score: number;
        selection_reason?: string;
        topology?: { kind: string };
      }>;
    };

    const anchor = activate.claims.find((item) => item.claim.id === anchorId);
    const conflict = activate.claims.find((item) => item.claim.id === conflictId);
    expect(anchor).toBeDefined();
    expect(conflict).toEqual(
      expect.objectContaining({
        source: 'claim_link',
        topology: expect.objectContaining({ kind: 'conflict' }),
      })
    );
    expect(conflict?.selection_reason).toContain('topology_kind=conflict');
    expect((conflict?.score ?? 0) < (anchor?.score ?? 0)).toBe(true);
  });

  it('shadows superseded claims during topology expansion', async () => {
    const oldText = 'legacy rule epsilon';
    const newText = 'replacement rule zeta';
    const queryText = 'legacy query epsilon';
    setEmbeddingService(
      createEmbeddingService({
        [oldText]: normalize([1, 0]),
        [newText]: normalize([-1, 0]),
        [queryText]: normalize([1, 0]),
      })
    );
    await applyPolicy();

    const oldId = await upsertKnowledge(oldText);
    const newId = await upsertKnowledge(newText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: newId,
      target_claim_id: oldId,
      link_type: 'supersedes',
    });

    const activate = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{
        claim: { id: string };
        source?: string;
        topology?: { kind: string; shadowed_claim_ids?: string[] };
      }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).not.toContain(oldId);
    expect(activate.claims.find((item) => item.claim.id === newId)).toEqual(
      expect.objectContaining({
        source: 'claim_link',
        topology: expect.objectContaining({
          kind: 'supersession',
          shadowed_claim_ids: expect.arrayContaining([oldId]),
        }),
      })
    );
  });

  it('persists topology metadata and caps walk depth at two hops', async () => {
    const aText = 'seed node theta';
    const bText = 'bridge node iota';
    const cText = 'bridge node kappa';
    const dText = 'beyond limit lambda';
    const queryText = 'seed query theta';
    setEmbeddingService(
      createEmbeddingService({
        [aText]: normalize([1, 0]),
        [bText]: normalize([-1, 0]),
        [cText]: normalize([-1, 0]),
        [dText]: normalize([-1, 0]),
        [queryText]: normalize([1, 0]),
      })
    );
    await applyPolicy();

    const aId = await upsertKnowledge(aText);
    const bId = await upsertKnowledge(bText);
    const cId = await upsertKnowledge(cText);
    const dId = await upsertKnowledge(dText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: aId,
      target_claim_id: bId,
      link_type: 'related',
    });
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: bId,
      target_claim_id: cId,
      link_type: 'related',
    });
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: cId,
      target_claim_id: dId,
      link_type: 'related',
    });

    const activate = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 4,
    }).then((result) => result.structuredContent)) as {
      active_context_id: string;
      claims: Array<{
        claim: { id: string };
        topology?: { path?: unknown[] };
      }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toEqual(
      expect.arrayContaining([aId, bId, cId])
    );
    expect(activate.claims.map((item) => item.claim.id)).not.toContain(dId);
    expect(
      activate.claims.find((item) => item.claim.id === cId)?.topology?.path?.length
    ).toBe(2);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT claim_id, topology_metadata
       FROM active_context_items
       WHERE active_context_id = $1
         AND topology_metadata IS NOT NULL
       ORDER BY rank ASC`,
      [activate.active_context_id]
    );
    const rows = reader.getRowObjects() as Array<{
      claim_id: string;
      topology_metadata: string | Record<string, unknown>;
    }>;
    const topologyByClaimId = new Map(
      rows.map((row) => [
        row.claim_id,
        typeof row.topology_metadata === 'string'
          ? (JSON.parse(row.topology_metadata) as { path?: unknown[] })
          : ((row.topology_metadata as { path?: unknown[] }) ?? {}),
      ])
    );
    expect(topologyByClaimId.has(bId)).toBe(true);
    expect(topologyByClaimId.has(cId)).toBe(true);
    expect(topologyByClaimId.get(cId)?.path?.length).toBe(2);
  });

  it('improves activate recall when topology walk is enabled', async () => {
    const seedText = 'effect seed anchor';
    const relatedText = 'effect linked expansion';
    const queryText = 'effect query anchor';
    const embeddingService = createEmbeddingService({
      [seedText]: normalize([1, 0]),
      [relatedText]: normalize([-1, 0]),
      [queryText]: normalize([1, 0]),
    });

    await resetTopologyTestState();
    setEmbeddingService(embeddingService);
    await applyPolicyWithTopologyEnabled(false);
    const withoutSeedId = await upsertKnowledge(seedText);
    const withoutRelatedId = await upsertKnowledge(relatedText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: withoutRelatedId,
      target_claim_id: withoutSeedId,
      link_type: 'related',
    });
    const withoutTopology = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{ claim: { id: string } }>;
    };

    await resetTopologyTestState();
    setEmbeddingService(embeddingService);
    await applyPolicy();
    const withSeedId = await upsertKnowledge(seedText);
    const withRelatedId = await upsertKnowledge(relatedText);
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: withRelatedId,
      target_claim_id: withSeedId,
      link_type: 'related',
    });
    const withTopology = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{ claim: { id: string }; source?: string }>;
    };

    expect(withoutTopology.claims.map((item) => item.claim.id)).toContain(withoutSeedId);
    expect(withoutTopology.claims.map((item) => item.claim.id)).not.toContain(withoutRelatedId);
    expect(withTopology.claims.map((item) => item.claim.id)).toEqual(
      expect.arrayContaining([withSeedId, withRelatedId])
    );
    expect(withTopology.claims.find((item) => item.claim.id === withRelatedId)?.source).toBe(
      'claim_link'
    );
  });

  it('does not expose filtered conflict ids through visible seed metadata', async () => {
    const anchorText = 'scope visible anchor';
    const hiddenConflictText = 'scope hidden conflict';
    const queryText = 'scope query anchor';
    setEmbeddingService(
      createEmbeddingService({
        [anchorText]: normalize([1, 0]),
        [hiddenConflictText]: normalize([-1, 0]),
        [queryText]: normalize([1, 0]),
      })
    );
    await applyPolicy();

    const anchorId = await upsertKnowledge(anchorText, { scope: 'project' });
    const hiddenConflictId = await upsertKnowledge(hiddenConflictText, { scope: 'principle' });
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: hiddenConflictId,
      target_claim_id: anchorId,
      link_type: 'contradicts',
    });

    const activate = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{
        claim: { id: string };
        topology?: { conflicts?: Array<{ claim_id: string }> };
      }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toContain(anchorId);
    expect(activate.claims.map((item) => item.claim.id)).not.toContain(hiddenConflictId);
    const anchor = activate.claims.find((item) => item.claim.id === anchorId);
    expect(anchor?.topology?.conflicts ?? []).not.toEqual(
      expect.arrayContaining([expect.objectContaining({ claim_id: hiddenConflictId })])
    );
  });

  it('does not shadow visible claims when the superseding claim is filtered out', async () => {
    const oldText = 'visible legacy rule';
    const hiddenNewText = 'hidden replacement rule';
    const queryText = 'visible legacy query';
    setEmbeddingService(
      createEmbeddingService({
        [oldText]: normalize([1, 0]),
        [hiddenNewText]: normalize([-1, 0]),
        [queryText]: normalize([1, 0]),
      })
    );
    await applyPolicy();

    const oldId = await upsertKnowledge(oldText, { scope: 'project' });
    const hiddenNewId = await upsertKnowledge(hiddenNewText, { scope: 'principle' });
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: hiddenNewId,
      target_claim_id: oldId,
      link_type: 'supersedes',
    });

    const activate = (await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: queryText,
      top_k: 3,
    }).then((result) => result.structuredContent)) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toContain(oldId);
    expect(activate.claims.map((item) => item.claim.id)).not.toContain(hiddenNewId);
  });
});

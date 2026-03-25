import { computeContentHash } from '@pce/embeddings';
import { beforeEach, describe, expect, it } from 'vitest';
import { dispatchTool, resetRetrievalPlannerTestState } from './helpers/retrievalPlannerTestUtils';
import { queryEntities } from '../src/store/entities';
import { hybridSearchWithScores } from '../src/store/hybridSearch';
import { autoLinkClaimEntities } from '../src/store/entityExtractor';

type ToolResponse = Awaited<ReturnType<typeof dispatchTool>>;
type ToolStructuredContent = NonNullable<ToolResponse['structuredContent']>;

type UpsertResult = {
  id: string;
  is_new: boolean;
};

type ObserveResult = {
  observation_id: string;
};

type DistillResult = {
  candidate_id: string;
};

type PromoteResult = {
  claim_id: string;
  is_new: boolean;
};

type ActivateResult = {
  claims: Array<{
    claim: {
      id: string;
    };
  }>;
};

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

function expectSuccess<T extends ToolStructuredContent>(result: ToolResponse): T {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent as T;
}

function buildPolicyYamlWithQueryExpansion(): string {
  return `
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
    query_expansion:
      enabled: true
      max_seed_entities: 1
      max_related_entities: 4
      max_expansion_terms: 4
`.trim();
}

function buildProvenance(at: string) {
  return {
    at,
    actor: 'claude',
  };
}

describe('pattern NLP entity extraction integration', () => {
  it('does not auto-create entities on upsert, but explicit extractor linking improves activate retrieval via query expansion', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: buildPolicyYamlWithQueryExpansion(),
    });

    const primaryText = 'hybridSearch.ts uses DuckDB for vector similarity';
    const primary = expectSuccess<UpsertResult>(
      await dispatchTool('pce_memory_upsert', {
        text: primaryText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(primaryText)}`,
        provenance: buildProvenance('2026-03-25T00:00:00.000Z'),
      })
    );
    const relatedText = 'hybridSearch.ts controls cosine similarity thresholds';
    const related = expectSuccess<UpsertResult>(
      await dispatchTool('pce_memory_upsert', {
        text: relatedText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(relatedText)}`,
        provenance: buildProvenance('2026-03-25T00:01:00.000Z'),
      })
    );
    await dispatchTool('pce_memory_upsert', {
      text: 'DuckDB office hours agenda for next quarter',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash('DuckDB office hours agenda for next quarter')}`,
      provenance: buildProvenance('2026-03-25T00:02:00.000Z'),
    });

    const entitiesBeforeExplicitLink = await queryEntities({
      claim_id: primary.id,
      limit: 10,
    });
    expect(entitiesBeforeExplicitLink).toHaveLength(0);

    const primaryLinkResult = await autoLinkClaimEntities(primary.id, primaryText);
    const relatedLinkResult = await autoLinkClaimEntities(related.id, relatedText);
    const linkedEntities = await queryEntities({
      claim_id: primary.id,
      limit: 10,
    });
    const linkedKeys = new Set(linkedEntities.map((entity) => entity.canonical_key));

    expect(primaryLinkResult.entityCount).toBeGreaterThan(0);
    expect(relatedLinkResult.entityCount).toBeGreaterThan(0);
    expect(linkedKeys.has('duckdb')).toBe(true);
    expect(linkedKeys.has('hybridsearch.ts')).toBe(true);

    const baseline = await hybridSearchWithScores(['project'], 3, 'duckdb', {
      enableRerank: false,
      includeBreakdown: true,
    });
    const baselineIds = baseline.map((item) => item.claim.id);

    const activated = expectSuccess<ActivateResult>(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        top_k: 3,
        q: 'duckdb',
      })
    );
    const activatedIds = activated.claims.map((item) => item.claim.id);

    expect(baselineIds).toContain(primary.id);
    expect(baselineIds).not.toContain(related.id);
    expect(activatedIds).toContain(primary.id);
    expect(activatedIds).toContain(related.id);
  });

  it('does not auto-create entities on promote until the extractor utility is called explicitly', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: buildPolicyYamlWithQueryExpansion(),
    });

    const observedText = 'Vitest verifies handleActivate behavior in pce-memory';
    const observation = expectSuccess<ObserveResult>(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: observedText,
        extract: { mode: 'noop' },
      })
    );
    const distilled = expectSuccess<DistillResult>(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [observation.observation_id],
      })
    );
    const promoted = expectSuccess<PromoteResult>(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distilled.candidate_id,
        provenance: buildProvenance('2026-03-25T00:10:00.000Z'),
      })
    );

    const entitiesBeforeExplicitLink = await queryEntities({
      claim_id: promoted.claim_id,
      limit: 10,
    });
    expect(entitiesBeforeExplicitLink).toHaveLength(0);

    const linkResult = await autoLinkClaimEntities(promoted.claim_id, observedText);
    const entities = await queryEntities({
      claim_id: promoted.claim_id,
      limit: 10,
    });
    const keys = new Set(entities.map((entity) => entity.canonical_key));

    expect(promoted.is_new).toBe(true);
    expect(linkResult.entityCount).toBeGreaterThan(0);
    expect(keys.has('vitest')).toBe(true);
    expect(keys.has('handleactivate')).toBe(true);
    expect(keys.has('pce-memory')).toBe(true);
  });

  it('keeps manually provided entities as the only links when the extractor utility is not called', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: buildPolicyYamlWithQueryExpansion(),
    });

    const upserted = expectSuccess<UpsertResult>(
      await dispatchTool('pce_memory_upsert', {
        text: 'DuckDB powers hybridSearch.ts',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash('DuckDB powers hybridSearch.ts')}`,
        provenance: buildProvenance('2026-03-25T00:20:00.000Z'),
        entities: [
          {
            id: 'ent_manual_only',
            type: 'Concept',
            name: 'Manual Only',
            canonical_key: 'manual-only',
          },
        ],
      })
    );

    const entities = await queryEntities({
      claim_id: upserted.id,
      limit: 10,
    });
    const keys = new Set(entities.map((entity) => entity.canonical_key));

    expect(entities).toHaveLength(1);
    expect(keys.has('manual-only')).toBe(true);
    expect(keys.has('duckdb')).toBe(false);
    expect(keys.has('hybridsearch.ts')).toBe(false);
  });
});

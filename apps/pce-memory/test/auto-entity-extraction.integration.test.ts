import { computeContentHash } from '@pce/embeddings';
import { beforeEach, describe, expect, it } from 'vitest';
import { dispatchTool, resetRetrievalPlannerTestState } from './helpers/retrievalPlannerTestUtils';
import { queryEntities } from '../src/store/entities';
import { hybridSearchWithScores } from '../src/store/hybridSearch';

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

describe('automatic entity extraction integration', () => {
  it('auto-creates entities on upsert and improves activate retrieval via query expansion', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: buildPolicyYamlWithQueryExpansion(),
    });

    const primary = expectSuccess<UpsertResult>(
      await dispatchTool('pce_memory_upsert', {
        text: 'hybridSearch.ts uses DuckDB for vector similarity',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(
          'hybridSearch.ts uses DuckDB for vector similarity'
        )}`,
        provenance: buildProvenance('2026-03-25T00:00:00.000Z'),
      })
    );
    const related = expectSuccess<UpsertResult>(
      await dispatchTool('pce_memory_upsert', {
        text: 'hybridSearch.ts controls cosine similarity thresholds',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(
          'hybridSearch.ts controls cosine similarity thresholds'
        )}`,
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

    const autoEntities = await queryEntities({
      claim_id: primary.id,
      limit: 10,
    });
    const autoKeys = new Set(autoEntities.map((entity) => entity.canonical_key));

    expect(autoKeys.has('duckdb')).toBe(true);
    expect(autoKeys.has('hybridsearch.ts')).toBe(true);

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

  it('auto-creates entities on promote', async () => {
    await dispatchTool('pce_memory_policy_apply', {
      yaml: buildPolicyYamlWithQueryExpansion(),
    });

    const observation = expectSuccess<ObserveResult>(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'Vitest verifies handleActivate behavior in pce-memory',
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

    const entities = await queryEntities({
      claim_id: promoted.claim_id,
      limit: 10,
    });
    const keys = new Set(entities.map((entity) => entity.canonical_key));

    expect(promoted.is_new).toBe(true);
    expect(keys.has('vitest')).toBe(true);
    expect(keys.has('handleactivate')).toBe(true);
    expect(keys.has('pce-memory')).toBe(true);
  });

  it('skips auto extraction when manual entities are provided', async () => {
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

import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { initRateState, resetRates } from '../src/store/rate';
import { saveClaimVector, setEmbeddingService } from '../src/store/hybridSearch';
import { updateCritic } from '../src/store/critic';

beforeEach(async () => {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

function createMockEmbeddingService(embedding: readonly number[]): EmbeddingService {
  return {
    embed: () => () =>
      Promise.resolve(
        E.right({
          embedding,
          modelVersion: 'mock-v1',
        })
      ),
  };
}

function buildPolicyYaml(
  hybrid: Partial<{
    alpha: number;
    threshold: number;
    k_txt: number;
    k_vec: number;
    k_final: number;
  }> = {}
): string {
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
    alpha: ${hybrid.alpha ?? 0.65}
    threshold: ${hybrid.threshold ?? 0.15}
    k_txt: ${hybrid.k_txt ?? 48}
    k_vec: ${hybrid.k_vec ?? 96}
    k_final: ${hybrid.k_final ?? 12}
    recency_half_life_days: 30
`.trim();
}

async function applyPolicy(
  hybrid: Partial<{
    alpha: number;
    threshold: number;
    k_txt: number;
    k_vec: number;
    k_final: number;
  }> = {}
): Promise<void> {
  await dispatchTool('pce_memory_policy_apply', { yaml: buildPolicyYaml(hybrid) });
}

async function upsertClaim(input: {
  text: string;
  kind?: 'fact' | 'preference' | 'task' | 'policy_hint';
  memory_type?: 'evidence' | 'working_state' | 'knowledge' | 'procedure' | 'norm';
}) {
  const result = await dispatchTool('pce_memory_upsert', {
    text: input.text,
    kind: input.kind ?? 'fact',
    scope: 'project',
    boundary_class: 'internal',
    ...(input.memory_type ? { memory_type: input.memory_type } : {}),
    content_hash: `sha256:${computeContentHash(input.text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z' },
  });

  return result.structuredContent?.id as string;
}

describe('intent-aware activate', () => {
  it('intent resume_task boosts working_state task claims', async () => {
    await applyPolicy();

    const taskId = await upsertClaim({
      text: 'billing cache task handoff',
      kind: 'task',
      memory_type: 'working_state',
    });
    await new Promise((resolve) => setTimeout(resolve, 10));
    const factId = await upsertClaim({
      text: 'billing cache architecture note',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    await updateCritic(taskId, 0.5, 0, 1);
    await updateCritic(factId, 0.5, 0, 1);

    const base = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'billing cache',
      top_k: 2,
    });
    const baseClaims = base.structuredContent?.claims as Array<{ claim: { id: string } }>;
    expect(baseClaims[0]?.claim.id).toBe(factId);

    const planned = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'billing cache',
      intent: 'resume_task',
      top_k: 2,
    });
    const plannedClaims = planned.structuredContent?.claims as Array<{ claim: { id: string } }>;

    expect(planned.structuredContent?.intent).toBe('resume_task');
    expect(plannedClaims[0]?.claim.id).toBe(taskId);
  });

  it('kind_filter reduces results to matching kinds', async () => {
    await applyPolicy();
    await upsertClaim({ text: 'kind filter task', kind: 'task', memory_type: 'working_state' });
    await upsertClaim({ text: 'kind filter fact', kind: 'fact', memory_type: 'knowledge' });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'kind filter',
      kind_filter: ['task'],
      top_k: 10,
    });
    const claims = result.structuredContent?.claims as Array<{ claim: { kind: string } }>;

    expect(claims).toHaveLength(1);
    expect(claims.every((item) => item.claim.kind === 'task')).toBe(true);
  });

  it('memory_type_filter reduces results to matching memory types', async () => {
    await applyPolicy();
    await upsertClaim({
      text: 'memory type procedure steps',
      kind: 'fact',
      memory_type: 'procedure',
    });
    await upsertClaim({
      text: 'memory type knowledge note',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'memory type',
      memory_type_filter: ['procedure'],
      top_k: 10,
    });
    const claims = result.structuredContent?.claims as Array<{
      claim: { memory_type?: string | null };
    }>;

    expect(claims).toHaveLength(1);
    expect(claims.every((item) => item.claim.memory_type === 'procedure')).toBe(true);
  });

  it('persists active_context_items with score breakdowns and source layers', async () => {
    await applyPolicy();
    await upsertClaim({
      text: 'persist active context metadata',
      kind: 'task',
      memory_type: 'working_state',
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'active context metadata',
      intent: 'resume_task',
      top_k: 5,
    });

    const responseClaims = result.structuredContent?.claims as Array<{
      source_layer?: string;
      score_breakdown?: { score_final?: number; intent?: { boost?: number } };
      selection_reason?: string;
    }>;
    expect(responseClaims[0]?.source_layer).toBe('meso');
    expect(responseClaims[0]?.score_breakdown?.score_final).toBeDefined();
    expect(responseClaims[0]?.selection_reason).toContain('intent=resume_task');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT source_layer, score, score_breakdown, selection_reason, rank
       FROM active_context_items
       WHERE active_context_id = $1
       ORDER BY rank`,
      [result.structuredContent?.active_context_id as string]
    );
    const rows = reader.getRowObjects() as Array<{
      source_layer: string | null;
      score: number | null;
      score_breakdown: string | null;
      selection_reason: string | null;
      rank: number | null;
    }>;

    expect(rows).toHaveLength(1);
    expect(rows[0]?.source_layer).toBe('meso');
    expect(rows[0]?.score).toBeGreaterThan(0);
    expect(rows[0]?.selection_reason).toContain('intent=resume_task');

    const breakdown = JSON.parse(rows[0]?.score_breakdown ?? '{}') as {
      s_text?: number;
      score_final?: number;
      intent?: { boost?: number };
    };
    expect(breakdown.s_text).toBeDefined();
    expect(breakdown.score_final).toBeDefined();
    expect(breakdown.intent?.boost).toBeGreaterThan(1);
  });

  it('policy threshold from retrieval.hybrid affects activate scoring', async () => {
    await applyPolicy({ threshold: 0.6 });
    await upsertClaim({
      text: 'threshold controlled claim',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'threshold controlled',
      top_k: 5,
    });

    expect(result.structuredContent?.claims_count).toBe(0);
  });

  it('policy alpha from retrieval.hybrid can prioritize vector matches', async () => {
    await applyPolicy({ alpha: 0.95 });
    setEmbeddingService(createMockEmbeddingService([1, 0]));

    const lexicalId = await upsertClaim({
      text: 'planner keyword lexical match',
      kind: 'fact',
      memory_type: 'knowledge',
    });
    const semanticId = await upsertClaim({
      text: 'semantic memory without the query token',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    await updateCritic(lexicalId, 0.5, 0, 1);
    await saveClaimVector(lexicalId, [-1, 0], 'mock-v1');
    await saveClaimVector(semanticId, [1, 0], 'mock-v1');

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'planner keyword',
      top_k: 5,
    });
    const claims = result.structuredContent?.claims as Array<{ claim: { id: string } }>;

    expect(claims[0]?.claim.id).toBe(semanticId);
  });

  it('policy k_txt from retrieval.hybrid limits lexical candidate pool', async () => {
    await applyPolicy({ k_txt: 1, threshold: 0.0 });
    await upsertClaim({ text: 'lexical pool first match', kind: 'fact', memory_type: 'knowledge' });
    await new Promise((resolve) => setTimeout(resolve, 10));
    await upsertClaim({
      text: 'lexical pool second match',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'lexical pool',
      top_k: 5,
    });

    expect(result.structuredContent?.claims_count).toBe(1);
  });

  it('policy k_vec from retrieval.hybrid limits vector candidate pool', async () => {
    await applyPolicy({ alpha: 1.0, threshold: 0.0, k_vec: 1 });
    setEmbeddingService(createMockEmbeddingService([1, 0]));

    const bestId = await upsertClaim({
      text: 'vector candidate one',
      kind: 'fact',
      memory_type: 'knowledge',
    });
    const secondId = await upsertClaim({
      text: 'vector candidate two',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    await saveClaimVector(bestId, [1, 0], 'mock-v1');
    await saveClaimVector(secondId, [0.8, 0.2], 'mock-v1');

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'semantic-only-query',
      top_k: 5,
    });
    const claims = result.structuredContent?.claims as Array<{ claim: { id: string } }>;

    expect(result.structuredContent?.claims_count).toBe(1);
    expect(claims[0]?.claim.id).toBe(bestId);
  });

  it('remains backward compatible when activate is called without new parameters', async () => {
    await applyPolicy();
    await upsertClaim({
      text: 'backward compatible activate',
      kind: 'fact',
      memory_type: 'knowledge',
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
    });

    expect(result.isError).toBeUndefined();
    expect(result.structuredContent?.claims_count).toBe(1);
    expect(result.structuredContent?.intent).toBeUndefined();
  });
});

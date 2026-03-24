import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../../src/core/handlers';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection';
import { resetLayerScopeState } from '../../src/state/layerScopeState';
import { resetMemoryState, transitionToHasClaims } from '../../src/state/memoryState';
import type { ClaimInput } from '../../src/store/claims';
import { upsertClaim } from '../../src/store/claims';
import { setEmbeddingService } from '../../src/store/hybridSearch';
import { initRateState, resetRates } from '../../src/store/rate';

export function createMockEmbeddingService(embedding: readonly number[]): EmbeddingService {
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

export async function resetRetrievalPlannerTestState(): Promise<void> {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '1000';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

export function buildPolicyYaml(
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

export async function applyPolicy(
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

export async function upsertClaimViaTool(input: {
  text: string;
  kind?: 'fact' | 'preference' | 'task' | 'policy_hint';
  memory_type?: 'evidence' | 'working_state' | 'knowledge' | 'procedure' | 'norm';
  boundary_class?: 'public' | 'internal' | 'pii';
  scope?: 'session' | 'project' | 'principle';
}) {
  return dispatchTool('pce_memory_upsert', {
    text: input.text,
    kind: input.kind ?? 'fact',
    scope: input.scope ?? 'project',
    boundary_class: input.boundary_class ?? 'internal',
    ...(input.memory_type ? { memory_type: input.memory_type } : {}),
    content_hash: `sha256:${computeContentHash(input.text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z' },
  });
}

export async function insertClaimDirect(input: ClaimInput): Promise<Awaited<ReturnType<typeof upsertClaim>>['claim']> {
  const result = await upsertClaim({
    ...input,
    content_hash: input.content_hash ?? `sha256:${computeContentHash(input.text)}`,
  });
  transitionToHasClaims(result.isNew);
  return result.claim;
}


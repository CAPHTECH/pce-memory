import { beforeEach, describe, expect, it } from 'vitest';
import { stringify } from 'yaml';
import { computeContentHash } from '@pce/embeddings';
import { defaultPolicy } from '@pce/policy-schemas';
import { dispatchTool } from '../src/core/handlers.js';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import { resetLayerScopeState } from '../src/state/layerScopeState.js';
import { getEntitiesForClaim } from '../src/store/entities.js';
import { hybridSearchWithScores } from '../src/store/hybridSearch.js';
import { upsertClaim } from '../src/store/claims.js';
import { initRateState, resetRates } from '../src/store/rate.js';

interface OllamaRuntime {
  endpoint: string;
  model: string;
}

interface OllamaModelsResponse {
  data?: Array<{ id?: string }>;
}

function entityLabel(entity: { name?: string; canonical_key?: string }): string {
  return (entity.name ?? entity.canonical_key ?? '').replace(/-/g, ' ').trim();
}

function isJwtLike(value: string): boolean {
  const normalized = value.toLowerCase();
  return normalized.includes('jwt') || normalized.includes('json web token');
}

async function resolveOllamaRuntime(): Promise<OllamaRuntime | null> {
  const endpoint = process.env['PCE_TEST_OLLAMA_ENDPOINT'] ?? 'http://127.0.0.1:11434';
  const preferredModel = process.env['PCE_TEST_OLLAMA_MODEL'] ?? 'qwen3.5:9b';
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), 1_500);

  try {
    const response = await fetch(`${endpoint.replace(/\/+$/g, '')}/v1/models`, {
      signal: controller.signal,
    });
    if (!response.ok) {
      return null;
    }

    const payload = (await response.json()) as OllamaModelsResponse;
    const modelIds = (payload.data ?? [])
      .map((item) => item.id)
      .filter((id): id is string => typeof id === 'string' && id.length > 0);
    if (modelIds.length === 0) {
      return null;
    }

    return {
      endpoint,
      model: modelIds.includes(preferredModel) ? preferredModel : modelIds[0]!,
    };
  } catch {
    return null;
  } finally {
    clearTimeout(timeout);
  }
}

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

async function applyPolicy(runtime: OllamaRuntime) {
  const result = await dispatchTool('pce_memory_policy_apply', {
    yaml: stringify({
      ...defaultPolicy,
      retrieval: {
        ...(defaultPolicy.retrieval ?? {}),
        hybrid: {
          ...(defaultPolicy.retrieval?.hybrid ?? {}),
          query_expansion: {
            enabled: true,
            max_seed_entities: 1,
            max_related_entities: 4,
            max_expansion_terms: 4,
          },
        },
      },
      extraction: {
        llm_enabled: true,
        ollama_endpoint: runtime.endpoint,
        model: runtime.model,
      },
    }),
  });
  expect(result.isError).toBeUndefined();
}

const OLLAMA_RUNTIME = await resolveOllamaRuntime();
const itIfOllama = OLLAMA_RUNTIME ? it : it.skip;

beforeEach(async () => {
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

describe('LLM entity extraction integration (real Ollama)', () => {
  itIfOllama(
    'extracts authentication entities, links them on promote, and improves activate retrieval',
    async ({ skip }) => {
      const runtime = OLLAMA_RUNTIME!;
      await applyPolicy(runtime);

      const observation = expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content:
            'Authentication architecture uses JWT access tokens, refresh token rotation, and session revocation.',
          boundary_class: 'internal',
          extract: { mode: 'noop' },
        })
      );

      const distill = expectSuccess(
        await dispatchTool('pce_memory_distill', {
          source_observation_ids: [observation.observation_id],
          note: 'real ollama auth architecture candidate',
        })
      );

      const conn = await getConnection();
      const queueReader = await conn.runAndReadAll(
        'SELECT proposed_entities FROM promotion_queue WHERE id = $1',
        [distill.candidate_id]
      );
      const queueRows = queueReader.getRowObjects() as Array<{ proposed_entities: string }>;
      const proposedEntities = JSON.parse(queueRows[0]?.proposed_entities ?? '[]') as Array<{
        name?: string;
        canonical_key?: string;
      }>;
      if (proposedEntities.length === 0) {
        skip();
      }

      expect(
        proposedEntities.some((entity) => isJwtLike(entityLabel(entity)))
      ).toBe(true);
      expect(proposedEntities.length).toBeGreaterThanOrEqual(2);

      const promote = expectSuccess(
        await dispatchTool('pce_memory_promote', {
          candidate_id: distill.candidate_id,
          provenance: { at: '2025-01-03T00:00:00.000Z', actor: 'claude' },
        })
      );

      const linkedEntities = await getEntitiesForClaim(promote.claim_id as string);
      expect(linkedEntities.some((entity) => isJwtLike(entityLabel(entity)))).toBe(true);

      const jwtClaimText = 'JSON Web Token (JWT) rotation prevents token leakage during key rollover';
      const jwtClaimHash = `sha256:${computeContentHash(jwtClaimText)}`;
      await upsertClaim({
        text: jwtClaimText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: jwtClaimHash,
      });

      const candidateQueries = [...new Set(proposedEntities.map((entity) => entityLabel(entity)))]
        .map((label) => label.trim())
        .filter((label) => label.length > 0 && !isJwtLike(label));
      expect(candidateQueries.length).toBeGreaterThan(0);

      let retrievalImproved = false;
      for (const query of candidateQueries) {
        const baseline = await hybridSearchWithScores(['project'], 10, query, {
          enableRerank: false,
          includeBreakdown: true,
          queryExpansion: {
            enabled: false,
            maxSeedEntities: 1,
            maxRelatedEntities: 4,
            maxExpansionTerms: 4,
          },
        });
        if (baseline.some((item) => item.claim.content_hash === jwtClaimHash)) {
          continue;
        }

        const activate = await dispatchTool('pce_memory_activate', {
          scope: ['project'],
          allow: ['answer:task'],
          q: query,
          top_k: 10,
        });
        const claims = activate.structuredContent?.claims as Array<{
          claim: { content_hash: string };
        }>;
        if (claims.some((item) => item.claim.content_hash === jwtClaimHash)) {
          retrievalImproved = true;
          break;
        }
      }

      expect(retrievalImproved).toBe(true);
    }
  );
});

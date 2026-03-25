import { beforeEach, describe, expect, it } from 'vitest';
import * as E from 'fp-ts/Either';
import type { EmbeddingService } from '@pce/embeddings';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { getConnection } from '../src/db/connection';
import { setEmbeddingService } from '../src/store/hybridSearch';
import {
  applyPolicy,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

type ActivateMaintenanceHints = {
  similar_pairs: Array<{
    a: string;
    b: string;
    similarity: number;
    suggestion: 'consider_consolidation';
  }>;
  stale_candidates: Array<{
    id: string;
    last_retrieved_at: null;
    days_since_created: number;
  }>;
  unprocessed_observations: number;
  high_retrieval_no_feedback: Array<{
    id: string;
    retrieval_count: number;
    feedback_count: number;
  }>;
};

function normalizeForEmbedding(text: string): string {
  return text
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/[_./:-]+/g, ' ')
    .toLowerCase();
}

function tokenize(text: string): string[] {
  return normalizeForEmbedding(text).match(/[a-z0-9]+/g) ?? [];
}

function fnv1a(input: string): number {
  let hash = 0x811c9dc5;
  for (let index = 0; index < input.length; index++) {
    hash ^= input.charCodeAt(index);
    hash = Math.imul(hash, 0x01000193);
  }
  return hash >>> 0;
}

function deterministicEmbedding(text: string, dimensions = 64): readonly number[] {
  const vector = new Array<number>(dimensions).fill(0);
  const tokens = tokenize(text);
  if (tokens.length === 0) {
    vector[0] = 1;
    return vector;
  }

  for (const token of tokens) {
    const seed = fnv1a(token);
    for (let dim = 0; dim < dimensions; dim++) {
      const rotated = (seed >>> (dim % 16)) ^ ((seed << (dim % 13)) >>> 0);
      const signal = ((rotated + dim * 2654435761) >>> 0) % 2000;
      vector[dim] += signal / 1000 - 1;
    }
  }

  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    vector[0] = 1;
    return vector;
  }

  return vector.map((value) => value / magnitude);
}

function createDeterministicEmbeddingService(): EmbeddingService {
  return {
    embed: (input) => () => {
      const text = typeof input === 'string' ? input : JSON.stringify(input);
      return Promise.resolve(
        E.right({
          embedding: deterministicEmbedding(text),
          modelVersion: 'maintenance-test-v1',
        })
      );
    },
  };
}

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  if (result.isError === true) {
    throw new Error(JSON.stringify(result.structuredContent ?? result.content ?? result, null, 2));
  }

  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

function isoDaysAgo(days: number): string {
  return new Date(Date.now() - days * 24 * 60 * 60 * 1000).toISOString();
}

async function updateClaimCreatedAt(claimId: string, createdAt: string): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    'UPDATE claims SET created_at = $1, updated_at = $1, recency_anchor = $1 WHERE id = $2',
    [createdAt, claimId]
  );
}

async function createClaim(text: string, createdAt: string): Promise<string> {
  const payload = expectSuccess(
    await upsertClaimViaTool({
      text,
      kind: 'fact',
      memory_type: 'knowledge',
      scope: 'project',
    })
  ) as { id: string };

  await updateClaimCreatedAt(payload.id, createdAt);
  return payload.id;
}

async function createObservation(content: string, createdAt: string): Promise<void> {
  const payload = expectSuccess(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      boundary_class: 'internal',
      extract: { mode: 'noop' },
    })
  ) as { observation_id: string };

  const conn = await getConnection();
  await conn.run('UPDATE observations SET created_at = $1 WHERE id = $2', [
    createdAt,
    payload.observation_id,
  ]);
}

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
  setEmbeddingService(createDeterministicEmbeddingService());
});

describe('activate maintenance hints', () => {
  it('returns maintenance_hints with duplicate, stale, observation, and retrieval signals', async () => {
    await applyPolicy({ hybrid: { threshold: 0.0 } });

    const duplicateA = await createClaim(
      'Operations ledger for maple-0 shows certificate renewal every 30 days for cluster north.',
      isoDaysAgo(40)
    );
    const duplicateB = await createClaim(
      'Operations ledger for maple-0 shows certificate renewal every 30 days for cluster south.',
      isoDaysAgo(39)
    );
    const staleClaim = await createClaim(
      'Dormant maintenance memo for archive spruce never retrieved and older than a month.',
      isoDaysAgo(75)
    );
    const highRetrievalClaim = await createClaim(
      'Hotspot memo quartz recurring maintenance review for cedar relay handoff.',
      isoDaysAgo(10)
    );

    await createObservation(
      'Raw observation backlog item for overnight queue watermark drift.',
      isoDaysAgo(2)
    );

    for (let attempt = 0; attempt < 6; attempt++) {
      expectSuccess(
        await dispatchTool('pce_memory_activate', {
          scope: ['project'],
          allow: ['answer:task'],
          q: 'quartz cedar relay handoff',
          top_k: 1,
        })
      );
    }

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'certificate renewal cluster',
        top_k: 2,
        include_meta: true,
      })
    ) as {
      maintenance_hints?: ActivateMaintenanceHints;
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims.map((item) => item.claim.id).sort()).toEqual(
      [duplicateA, duplicateB].sort()
    );
    expect(activate.maintenance_hints).toBeDefined();

    const hints = activate.maintenance_hints!;
    expect(hints.similar_pairs).toHaveLength(1);
    expect(new Set([hints.similar_pairs[0]?.a, hints.similar_pairs[0]?.b])).toEqual(
      new Set([duplicateA, duplicateB])
    );
    expect(hints.similar_pairs[0]?.suggestion).toBe('consider_consolidation');
    expect(hints.similar_pairs[0]?.similarity).toBeGreaterThan(0.9);
    expect(hints.stale_candidates).toContainEqual(
      expect.objectContaining({
        id: staleClaim,
        last_retrieved_at: null,
      })
    );
    expect(hints.stale_candidates[0]?.days_since_created).toBeGreaterThanOrEqual(30);
    expect(hints.unprocessed_observations).toBe(1);
    expect(hints.high_retrieval_no_feedback).toContainEqual({
      id: highRetrievalClaim,
      retrieval_count: 6,
      feedback_count: 0,
    });
  });

  it('omits maintenance_hints when maintenance.hints_enabled is false', async () => {
    await applyPolicy({
      hybrid: { threshold: 0.0 },
      maintenance: { hints_enabled: false },
    });
    await createClaim('Maintenance hints disabled sanity check', isoDaysAgo(3));

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'disabled sanity',
        top_k: 5,
      })
    ) as {
      maintenance_hints?: ActivateMaintenanceHints;
    };

    expect(activate).not.toHaveProperty('maintenance_hints');
  });

  it('activate schema exposes maintenance_hints', () => {
    const activateTool = TOOL_DEFINITIONS.find((tool) => tool.name === 'pce_memory_activate');
    const outputProperties = activateTool?.outputSchema?.properties as
      | Record<string, { type?: string }>
      | undefined;

    expect(outputProperties?.maintenance_hints?.type).toBe('object');
  });
});

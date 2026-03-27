import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../src/core/handlers';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';
import { setEmbeddingService } from '../src/store/hybridSearch';

const ANCHOR_TEXT =
  'Connectivity anchor: maple login tokens require issuer validation and short session expiry.';
const RELATED_TEXT =
  'Connectivity extension: orchard renewal ledgers extend maple access controls with revocation windows.';
const PROMOTED_TEXT =
  'Connectivity promoted note: orchard renewal ledgers extend maple access controls with revocation windows.';
const DISTRACTOR_TEXT =
  'Connectivity distractor: maple login token onboarding checklist for support handoff.';
const QUERY_TEXT = 'maple login token issuer validation handoff';

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function normalizeForDeterministicEmbedding(text: string): string {
  return text
    .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
    .replace(/[_./:-]+/g, ' ')
    .toLowerCase();
}

function tokenizeDeterministic(text: string): string[] {
  return normalizeForDeterministicEmbedding(text).match(/[a-z0-9]+/g) ?? [];
}

function fnv1aDeterministic(input: string): number {
  let hash = 0x811c9dc5;
  for (let index = 0; index < input.length; index++) {
    hash ^= input.charCodeAt(index);
    hash = Math.imul(hash, 0x01000193);
  }
  return hash >>> 0;
}

function deterministicEmbedding(text: string, dimensions = 64): readonly number[] {
  const vector = new Array<number>(dimensions).fill(0);
  const tokens = tokenizeDeterministic(text);
  if (tokens.length === 0) {
    vector[0] = 1;
    return vector;
  }

  for (const token of tokens) {
    const baseHash = fnv1aDeterministic(token);
    const index = baseHash % dimensions;
    const sign = (fnv1aDeterministic(`${token}:sign`) & 1) === 0 ? 1 : -1;
    vector[index] += sign;
  }

  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    vector[0] = 1;
    return vector;
  }

  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createLookupEmbeddingService(
  embeddings: Record<string, readonly number[]>
): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      async () =>
        E.right({
          embedding: embeddings[text] ?? normalize([0, 1]),
          modelVersion: 'claim-connectivity-test-v1',
        }),
  };
}

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
  setEmbeddingService(
    createLookupEmbeddingService({
      [ANCHOR_TEXT]: normalize([1, 0]),
      [RELATED_TEXT]: normalize([0.6, 0.8]),
      [PROMOTED_TEXT]: normalize([0.6, 0.8]),
      [DISTRACTOR_TEXT]: normalize([1, 1]),
      [QUERY_TEXT]: normalize([1, -1]),
    })
  );
  await dispatchTool('pce_memory_policy_apply', {});
});

async function upsertKnowledge(text: string): Promise<{
  id: string;
  suggested_links: Array<{ target: string; similarity: number; suggested_type: 'related' }>;
}> {
  const result = await dispatchTool('pce_memory_upsert', {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
  });

  return result.structuredContent as {
    id: string;
    suggested_links: Array<{ target: string; similarity: number; suggested_type: 'related' }>;
  };
}

async function promoteObservation(content: string): Promise<{
  claim_id: string;
  suggested_links: Array<{ target: string; similarity: number; suggested_type: 'related' }>;
}> {
  const observe = await dispatchTool('pce_memory_observe', {
    source_type: 'chat',
    boundary_class: 'internal',
    content,
  });
  const observationId = observe.structuredContent?.observation_id as string;

  const distill = await dispatchTool('pce_memory_distill', {
    source_observation_ids: [observationId],
    proposed_kind: 'fact',
    proposed_scope: 'project',
    proposed_memory_type: 'knowledge',
  });
  const candidateId = distill.structuredContent?.candidate_id as string;

  const promote = await dispatchTool('pce_memory_promote', {
    candidate_id: candidateId,
    provenance: {
      at: '2025-01-02T00:00:00.000Z',
      actor: 'vitest',
    },
  });

  return promote.structuredContent as {
    claim_id: string;
    suggested_links: Array<{ target: string; similarity: number; suggested_type: 'related' }>;
  };
}

describe('claim connectivity', () => {
  it('suggests related claim links on upsert for new claims in the similarity band', async () => {
    const anchor = await upsertKnowledge(ANCHOR_TEXT);
    const related = await upsertKnowledge(RELATED_TEXT);

    expect(anchor.suggested_links).toEqual([]);
    expect(related.suggested_links).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          target: anchor.id,
          suggested_type: 'related',
        }),
      ])
    );
    const suggestion = related.suggested_links.find((item) => item.target === anchor.id);
    expect(suggestion?.similarity).toBeGreaterThanOrEqual(0.7);
    expect(suggestion?.similarity).toBeLessThan(0.85);
  });

  it('suggests related claim links on promote for newly created durable claims', async () => {
    const anchor = await upsertKnowledge(ANCHOR_TEXT);
    const promoted = await promoteObservation(PROMOTED_TEXT);

    expect(promoted.suggested_links).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          target: anchor.id,
          suggested_type: 'related',
        }),
      ])
    );
  });

  it('annotates activate results with explicit claim-link metadata for connected claims', async () => {
    const anchor = await upsertKnowledge(ANCHOR_TEXT);
    const related = await upsertKnowledge(RELATED_TEXT);
    await upsertKnowledge(DISTRACTOR_TEXT);

    const linkResult = await dispatchTool('pce_memory_link_claims', {
      source_claim_id: related.id,
      target_claim_id: anchor.id,
      link_type: 'related',
    });
    expect(linkResult.structuredContent?.link_type).toBe('related');

    const activate = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: QUERY_TEXT,
      top_k: 3,
      include_meta: true,
    });

    const claims = activate.structuredContent?.claims as Array<{
      claim: { id: string };
      source?: string;
      link?: { via_claim_id: string; link_type: string };
      selection_reason?: string;
    }>;

    expect(claims).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          claim: expect.objectContaining({ id: anchor.id }),
        }),
        expect.objectContaining({
          claim: expect.objectContaining({ id: related.id }),
          link: expect.objectContaining({
            via_claim_id: anchor.id,
            link_type: 'related',
          }),
        }),
      ])
    );
    const relatedClaim = claims.find((item) => item.claim.id === related.id);
    expect(relatedClaim?.selection_reason).toContain('link_type=related');
  });

  it('preserves higher-ranked direct hits under the duplicate-heavy connectivity benchmark pattern', async () => {
    setEmbeddingService({
      embed:
        ({ text }) =>
        async () =>
          E.right({
            embedding: deterministicEmbedding(text),
            modelVersion: 'deterministic-bow-v1',
          }),
    });

    let expectedAnchorId = '';
    let expectedRelatedId = '';

    for (let topic = 0; topic < 10; topic++) {
      const anchorText = `Connectivity anchor ${topic}: maple-${topic} login tokens require issuer validation and short session expiry.`;
      const relatedText = `Connectivity extension ${topic}: maple-${topic} refresh rotation extends login token controls with revocation windows and renewal ledgers.`;
      const anchor = await upsertKnowledge(anchorText);
      const related = await upsertKnowledge(relatedText);

      if (topic === 5) {
        expectedAnchorId = anchor.id;
        expectedRelatedId = related.id;
      }

      if (related.suggested_links.some((item) => item.target === anchor.id)) {
        await dispatchTool('pce_memory_link_claims', {
          source_claim_id: related.id,
          target_claim_id: anchor.id,
          link_type: 'related',
        });
      }
    }

    const activate = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'maple-5 login tokens issuer validation',
      top_k: 5,
      include_meta: true,
    });

    const claims = activate.structuredContent?.claims as Array<{
      claim: { id: string };
      source?: string;
      link?: { via_claim_id: string; link_type: string };
    }>;

    expect(claims.map((item) => item.claim.id)).toContain(expectedAnchorId);
    expect(claims.map((item) => item.claim.id)).not.toContain(expectedRelatedId);
    expect(claims.every((item) => item.source === 'search')).toBe(true);
  });
});

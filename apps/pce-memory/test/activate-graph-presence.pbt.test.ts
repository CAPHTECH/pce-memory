import { afterEach, describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import type { Claim } from '../src/store/claims';
import type { TopologyScoreBreakdown } from '../src/store/rerank';
import type { ActivateSearchItem } from '../src/core/handlers/shared';
import { ensureClaimLinkPresence } from '../src/core/handlers/shared';

function makeClaim(id: string): Claim {
  return {
    id,
    text: id,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    status: 'active',
    content_hash: `sha256:${id}`,
    utility: 0,
    confidence: 0.5,
    created_at: '2025-01-01T00:00:00.000Z',
    updated_at: '2025-01-01T00:00:00.000Z',
    recency_anchor: '2025-01-01T00:00:00.000Z',
    retrieval_count: 0,
  };
}

function makeTopology(pathScore: number, id: string): TopologyScoreBreakdown {
  return {
    seed_claim_id: `seed-${id}`,
    kind: 'support',
    depth: 1,
    hop_decay: 0.75,
    multiplier: pathScore,
    path_score: pathScore,
    path: [
      {
        kind: 'claim_link',
        from_claim_id: `seed-${id}`,
        to_claim_id: id,
        weight: 0.35,
        confidence: 1,
      },
    ],
  };
}

function makeItem(input: {
  id: string;
  score: number;
  source?: ActivateSearchItem['source'];
  topology?: TopologyScoreBreakdown;
  link?: ActivateSearchItem['link'];
}): ActivateSearchItem {
  return {
    claim: makeClaim(input.id),
    score: input.score,
    ...(input.source ? { source: input.source } : {}),
    ...(input.topology ? { topology: input.topology } : {}),
    ...(input.link ? { link: input.link } : {}),
  };
}

function ids(items: ActivateSearchItem[]): string[] {
  return items.map((item) => item.claim.id);
}

describe('ensureClaimLinkPresence properties', () => {
  const originalForceGraphPresence = process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE;

  afterEach(() => {
    if (originalForceGraphPresence === undefined) {
      delete process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE;
      return;
    }
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = originalForceGraphPresence;
  });

  it('Property: a full page is never displaced by lower-ranked graph candidates', async () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    await fc.assert(
      fc.asyncProperty(
        fc.integer({ min: 2, max: 6 }),
        fc.uniqueArray(fc.stringMatching(/direct-[a-z0-9]{1,8}/), {
          minLength: 2,
          maxLength: 6,
        }),
        fc.uniqueArray(fc.stringMatching(/graph-[a-z0-9]{1,8}/), {
          minLength: 1,
          maxLength: 6,
        }),
        async (rawTopK, directIds, graphIds) => {
          const topK = Math.min(rawTopK, directIds.length);
          const pageResults = directIds.slice(0, topK).map((id, index) =>
            makeItem({
              id,
              score: 1 - index * 0.05,
              source: 'search',
            })
          );
          const graphResults = graphIds.map((id, index) =>
            makeItem({
              id,
              score: 0.1 + index * 0.01,
              source: 'search',
              topology: makeTopology(0.2 + index * 0.1, id),
              link: {
                id: `link-${id}`,
                via_claim_id: pageResults[0]!.claim.id,
                link_type: 'related',
                confidence: 1,
              },
            })
          );

          const result = ensureClaimLinkPresence(
            pageResults,
            [...pageResults, ...graphResults],
            topK
          );

          expect(result).toEqual(pageResults);
        }
      ),
      { numRuns: 50 }
    );
  });

  it('Property: open-slot injection preserves existing ids and fills with the strongest graph candidate', async () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    await fc.assert(
      fc.asyncProperty(
        fc.integer({ min: 2, max: 6 }),
        fc.uniqueArray(fc.stringMatching(/page-[a-z0-9]{1,8}/), {
          minLength: 1,
          maxLength: 4,
        }),
        fc.uniqueArray(fc.stringMatching(/candidate-[a-z0-9]{1,8}/), {
          minLength: 1,
          maxLength: 5,
        }),
        async (topK, pageIds, candidateIds) => {
          const boundedPageIds = pageIds.slice(0, Math.max(1, topK - 1));
          const pageResults = boundedPageIds.map((id, index) =>
            makeItem({
              id,
              score: 0.9 - index * 0.05,
              source: 'search',
            })
          );
          const graphResults = candidateIds.map((id, index) =>
            makeItem({
              id,
              score: 0.2 - index * 0.01,
              source: 'search',
              topology: makeTopology(1 + index, id),
              link: {
                id: `link-${id}`,
                via_claim_id: pageResults[0]!.claim.id,
                link_type: 'related',
                confidence: 1,
              },
            })
          );
          const winner = graphResults[graphResults.length - 1]!;

          const result = ensureClaimLinkPresence(
            pageResults,
            [...pageResults, ...graphResults],
            topK
          );

          expect(result).toHaveLength(pageResults.length + 1);
          expect(new Set(ids(result))).toEqual(new Set([...ids(pageResults), winner.claim.id]));
          const injected = result.find((item) => item.claim.id === winner.claim.id);
          expect(injected?.source).toBe('claim_link');
        }
      ),
      { numRuns: 50 }
    );
  });

  it('Property: an existing graph-derived page item makes the helper a no-op', async () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    await fc.assert(
      fc.asyncProperty(
        fc.integer({ min: 2, max: 6 }),
        fc.uniqueArray(fc.stringMatching(/plain-[a-z0-9]{1,8}/), {
          minLength: 1,
          maxLength: 4,
        }),
        fc.stringMatching(/graph-on-page-[a-z0-9]{1,8}/),
        fc.uniqueArray(fc.stringMatching(/extra-[a-z0-9]{1,8}/), {
          minLength: 1,
          maxLength: 4,
        }),
        async (topK, plainIds, graphId, extraIds) => {
          const boundedPlainIds = plainIds.slice(0, Math.max(0, topK - 2));
          const graphItem = makeItem({
            id: graphId,
            score: 0.5,
            source: 'claim_link',
            topology: makeTopology(0.5, graphId),
            link: {
              id: `link-${graphId}`,
              via_claim_id: boundedPlainIds[0] ?? 'seed',
              link_type: 'related',
              confidence: 1,
            },
          });
          const pageResults = [
            ...boundedPlainIds.map((id, index) =>
              makeItem({
                id,
                score: 0.9 - index * 0.05,
                source: 'search',
              })
            ),
            graphItem,
          ];
          const extraGraphResults = extraIds.map((id, index) =>
            makeItem({
              id,
              score: 0.2 - index * 0.01,
              source: 'search',
              topology: makeTopology(1 + index, id),
              link: {
                id: `link-${id}`,
                via_claim_id: graphId,
                link_type: 'related',
                confidence: 1,
              },
            })
          );

          const result = ensureClaimLinkPresence(
            pageResults,
            [...pageResults, ...extraGraphResults],
            topK
          );

          expect(result).toEqual(pageResults);
        }
      ),
      { numRuns: 50 }
    );
  });
});

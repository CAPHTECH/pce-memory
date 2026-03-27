import { describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import type { Claim } from '../src/store/claims';
import type { ActivateSearchItem } from '../src/core/handlers/shared';
import { pageActivateResults } from '../src/core/handlers/shared';

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

function makeGraphItem(id: string, score: number): ActivateSearchItem {
  return {
    claim: makeClaim(id),
    score,
    source: 'claim_link',
    link: {
      id: `clk_${id}`,
      via_claim_id: 'seed',
      link_type: 'related',
      confidence: 1,
    },
    topology: {
      seed_claim_id: 'seed',
      kind: 'support',
      depth: 1,
      hop_decay: 0.75,
      multiplier: 0.2625,
      path_score: score * 0.2625,
      path: [
        {
          kind: 'claim_link',
          from_claim_id: 'seed',
          to_claim_id: id,
          link_id: `clk_${id}`,
          link_type: 'related',
          weight: 0.35,
          confidence: 1,
        },
      ],
    },
  };
}

function makeDirectItem(id: string, score: number): ActivateSearchItem {
  return {
    claim: makeClaim(id),
    score,
    source: 'search',
  };
}

describe('activate pagination graph presence properties', () => {
  it('Property: later pages never repeat a graph claim already returned on an earlier page', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.integer({ min: 2, max: 5 }),
        fc.integer({ min: 1, max: 4 }),
        async (topK, trailingCount) => {
          const results: ActivateSearchItem[] = [
            makeGraphItem('graph-early', 1000),
            ...Array.from({ length: topK - 1 }, (_, index) =>
              makeDirectItem(`front-${index}`, 900 - index)
            ),
            ...Array.from({ length: trailingCount }, (_, index) =>
              makeDirectItem(`tail-${index}`, 700 - index)
            ),
          ];

          const firstPage = pageActivateResults({ results, topK });
          const secondPage = pageActivateResults({
            results,
            topK,
            cursor: firstPage.nextCursor,
          });

          const firstIds = new Set(firstPage.searchResults.map((item) => item.claim.id));
          for (const item of secondPage.searchResults) {
            expect(firstIds.has(item.claim.id)).toBe(false);
          }
        }
      ),
      { numRuns: 40 }
    );
  });
});

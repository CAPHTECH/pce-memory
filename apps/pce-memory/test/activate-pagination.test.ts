import { describe, expect, it } from 'vitest';
import type { Claim } from '../src/store/claims';
import type { ActivateSearchItem } from '../src/core/handlers/shared';
import {
  pageActivateResults,
  pageActivateResultsWithObservationCap,
} from '../src/core/handlers/shared';

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

function makeItem(input: {
  id: string;
  score: number;
  source?: ActivateSearchItem['source'];
  link?: ActivateSearchItem['link'];
  topology?: ActivateSearchItem['topology'];
}): ActivateSearchItem {
  return {
    claim: makeClaim(input.id),
    score: input.score,
    ...(input.source ? { source: input.source } : {}),
    ...(input.link ? { link: input.link } : {}),
    ...(input.topology ? { topology: input.topology } : {}),
  };
}

function makeGraphItem(id: string, score: number): ActivateSearchItem {
  return makeItem({
    id,
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
  });
}

describe('activate pagination with graph presence', () => {
  it('does not re-inject a graph claim from an earlier durable-only page', () => {
    const results = [
      makeGraphItem('graph-early', 0.9),
      makeItem({ id: 'direct-1', score: 0.8, source: 'search' }),
      makeItem({ id: 'direct-2', score: 0.7, source: 'search' }),
    ];

    const firstPage = pageActivateResults({
      results,
      topK: 2,
    });
    expect(firstPage.searchResults.map((item) => item.claim.id)).toEqual(['graph-early', 'direct-1']);

    const secondPage = pageActivateResults({
      results,
      topK: 2,
      cursor: firstPage.nextCursor,
    });

    expect(secondPage.searchResults.map((item) => item.claim.id)).toEqual(['direct-2']);
  });

  it('does not re-inject a graph claim from an earlier observation-capped page', () => {
    const durableResults = [
      makeGraphItem('graph-early', 0.9),
      makeItem({ id: 'direct-1', score: 0.8, source: 'search' }),
      makeItem({ id: 'direct-2', score: 0.7, source: 'search' }),
    ];
    const observationResults = [
      makeItem({ id: 'obs-1', score: 0.6, source: 'observation' }),
      makeItem({ id: 'obs-2', score: 0.5, source: 'observation' }),
    ];

    const firstPage = pageActivateResultsWithObservationCap({
      durableResults,
      observationResults,
      topK: 4,
    });
    expect(firstPage.searchResults.map((item) => item.claim.id)).toEqual([
      'graph-early',
      'direct-1',
      'direct-2',
      'obs-1',
    ]);

    const secondPage = pageActivateResultsWithObservationCap({
      durableResults,
      observationResults,
      topK: 4,
      cursor: firstPage.nextCursor,
    });

    expect(secondPage.searchResults.map((item) => item.claim.id)).toEqual(['obs-2']);
  });
});

import { afterEach, describe, expect, it } from 'vitest';
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

function makeTopology(pathScore: number): TopologyScoreBreakdown {
  return {
    seed_claim_id: 'seed',
    kind: 'support',
    depth: 1,
    hop_decay: 0.75,
    multiplier: pathScore,
    path_score: pathScore,
    path: [
      {
        kind: 'claim_link',
        from_claim_id: 'seed',
        to_claim_id: 'graph',
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

describe('ensureClaimLinkPresence', () => {
  const originalForceGraphPresence = process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE;

  afterEach(() => {
    if (originalForceGraphPresence === undefined) {
      delete process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE;
      return;
    }
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = originalForceGraphPresence;
  });

  it('does not replace a full page with a lower-ranked graph candidate', () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    const pageResults = [
      makeItem({ id: 'direct-relevant', score: 0.92, source: 'search' }),
      makeItem({ id: 'seed', score: 0.9, source: 'search' }),
    ];
    const allResults = [
      ...pageResults,
      makeItem({
        id: 'noisy-related',
        score: 0.2,
        source: 'search',
        topology: makeTopology(0.2),
        link: {
          id: 'link-1',
          via_claim_id: 'seed',
          link_type: 'related',
          confidence: 1,
        },
      }),
    ];

    const result = ensureClaimLinkPresence(pageResults, allResults, 2);

    expect(result.map((item) => item.claim.id)).toEqual(['direct-relevant', 'seed']);
    expect(result.every((item) => item.source === 'search')).toBe(true);
  });

  it('fills an open slot with the best graph candidate', () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    const pageResults = [makeItem({ id: 'seed', score: 0.9, source: 'search' })];
    const allResults = [
      ...pageResults,
      makeItem({
        id: 'related-context',
        score: 0.2,
        source: 'search',
        topology: makeTopology(0.2),
        link: {
          id: 'link-2',
          via_claim_id: 'seed',
          link_type: 'related',
          confidence: 1,
        },
      }),
    ];

    const result = ensureClaimLinkPresence(pageResults, allResults, 2);

    expect(result.map((item) => item.claim.id)).toEqual(['seed', 'related-context']);
    expect(result[1]?.source).toBe('claim_link');
  });

  it('leaves the page unchanged when a graph-derived claim is already present', () => {
    process.env.PCE_ACTIVATE_FORCE_GRAPH_PRESENCE = '1';

    const graphItem = makeItem({
      id: 'related-context',
      score: 0.3,
      source: 'claim_link',
      topology: makeTopology(0.3),
      link: {
        id: 'link-3',
        via_claim_id: 'seed',
        link_type: 'related',
        confidence: 1,
      },
    });
    const pageResults = [makeItem({ id: 'seed', score: 0.9, source: 'search' }), graphItem];

    const result = ensureClaimLinkPresence(pageResults, pageResults, 2);

    expect(result).toEqual(pageResults);
  });
});

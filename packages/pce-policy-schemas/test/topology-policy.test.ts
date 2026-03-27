import { describe, expect, it } from 'vitest';
import { defaultPolicy, parsePolicy, validatePolicy } from '../src/index';

function cloneDefaultPolicy(): Record<string, unknown> {
  return JSON.parse(JSON.stringify(defaultPolicy)) as Record<string, unknown>;
}

describe('topology policy validation', () => {
  it('accepts topology policy blocks during parse', () => {
    const result = parsePolicy(
      `
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
    topology:
      enabled: true
      mode: walk
      seed_k: 6
      max_hops: 2
      hop_decay: 0.75
      include_paths: true
      edge_policy:
        supports:
          weight: 0.9
          direction: forward
          action: boost
        contradicts:
          action: flag_conflict
        supersedes:
          action: shadow_old
`.trim()
    );

    expect(result.ok).toBe(true);
    expect(result.value?.retrieval?.hybrid?.topology).toEqual(
      expect.objectContaining({
        enabled: true,
        mode: 'walk',
        seed_k: 6,
        max_hops: 2,
        hop_decay: 0.75,
        include_paths: true,
      })
    );
  });

  it('rejects invalid topology direction and action values', () => {
    const policy = cloneDefaultPolicy();
    policy['retrieval'] = {
      hybrid: {
        topology: {
          edge_policy: {
            supports: {
              direction: 'backward',
            },
            contradicts: {
              action: 'invert',
            },
          },
        },
      },
    };

    const result = validatePolicy(policy);
    expect(result.ok).toBe(false);
    expect(result.errors).toEqual(
      expect.arrayContaining([
        expect.stringContaining('topology.edge_policy.supports.direction'),
        expect.stringContaining('topology.edge_policy.contradicts.action'),
      ])
    );
  });

  it('rejects array-shaped retrieval and unknown topology keys', () => {
    const policy = cloneDefaultPolicy();
    policy['retrieval'] = [];

    const arrayResult = validatePolicy(policy);
    expect(arrayResult.ok).toBe(false);
    expect(arrayResult.errors).toEqual(expect.arrayContaining(['retrieval must be object']));

    const nestedPolicy = cloneDefaultPolicy();
    nestedPolicy['retrieval'] = {
      hybrid: {
        topology: {
          max_hops: 3,
          seed_k: 1.5,
          hop_decay: 1.5,
          extra_key: true,
          edge_policy: {
            supports: {
              weight: 0.9,
              direction: 'forward',
              action: 'boost',
              unknown: true,
            },
            typo: {
              action: 'boost',
            },
          },
        },
      },
    };

    const nestedResult = validatePolicy(nestedPolicy);
    expect(nestedResult.ok).toBe(false);
    expect(nestedResult.errors).toEqual(
      expect.arrayContaining([
        expect.stringContaining('retrieval.hybrid.topology.extra_key'),
        expect.stringContaining('topology.max_hops must be between 0 and 2'),
        expect.stringContaining('topology.seed_k must be integer'),
        expect.stringContaining('topology.hop_decay must be greater than 0 and at most 1'),
        expect.stringContaining('topology.edge_policy.supports.unknown'),
        expect.stringContaining('topology.edge_policy.typo is not allowed'),
      ])
    );
  });

  it('rejects array-shaped boundary blocks', () => {
    const policy = cloneDefaultPolicy();
    policy['boundary'] = [];

    const result = validatePolicy(policy);
    expect(result.ok).toBe(false);
    expect(result.errors).toEqual(expect.arrayContaining(['boundary must be object']));
  });

  it('rejects retrieval-level typos and non-finite topology integers', () => {
    const policy = cloneDefaultPolicy();
    policy['retrieval'] = {
      hybird: {},
      hybrid: {
        topology: {
          seed_k: Number.POSITIVE_INFINITY,
        },
      },
    };

    const result = validatePolicy(policy);
    expect(result.ok).toBe(false);
    expect(result.errors).toEqual(
      expect.arrayContaining(['retrieval.hybird is not allowed', 'topology.seed_k must be number'])
    );
  });

  it('returns validation errors instead of throwing on null edge_policy', () => {
    const policy = cloneDefaultPolicy();
    policy['retrieval'] = {
      hybrid: {
        topology: {
          edge_policy: null,
        },
      },
    };

    expect(() => validatePolicy(policy)).not.toThrow();
    const result = validatePolicy(policy);
    expect(result.ok).toBe(false);
    expect(result.errors).toEqual(expect.arrayContaining(['topology.edge_policy must be object']));
  });
});

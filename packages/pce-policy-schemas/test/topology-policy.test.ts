import { describe, expect, it } from 'vitest';
import { defaultPolicy, parsePolicy, validatePolicy } from '../src/index';

describe('topology policy validation', () => {
  it('accepts topology policy blocks during parse', () => {
    const result = parsePolicy(`
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
`.trim());

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
    const policy = structuredClone(defaultPolicy) as Record<string, unknown>;
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
});

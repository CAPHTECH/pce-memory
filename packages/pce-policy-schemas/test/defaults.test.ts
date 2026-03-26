/**
 * pce-policy-schemas/defaults.ts のテスト
 */
import { describe, it, expect } from 'vitest';
import {
  defaultPolicy,
  defaultBoundaryPolicy,
  defaultRetrievalPolicy,
  defaultMaintenancePolicy,
} from '../src/defaults';

describe('defaultPolicy', () => {
  it('has version 0.1', () => {
    expect(defaultPolicy.version).toBe('0.1');
  });

  it('has boundary config with scopes', () => {
    expect(defaultPolicy.boundary.scopes).toBeDefined();
    expect(defaultPolicy.boundary.scopes.session).toBeDefined();
    expect(defaultPolicy.boundary.scopes.project).toBeDefined();
    expect(defaultPolicy.boundary.scopes.principle).toBeDefined();
  });

  it('has boundary_classes', () => {
    expect(defaultPolicy.boundary.boundary_classes).toBeDefined();
    expect(defaultPolicy.boundary.boundary_classes.public.allow).toContain('*');
    expect(defaultPolicy.boundary.boundary_classes.secret.allow).toEqual([]);
  });
});

describe('defaultBoundaryPolicy', () => {
  it('returns boundary from defaultPolicy', () => {
    const bp = defaultBoundaryPolicy();
    expect(bp).toBe(defaultPolicy.boundary);
  });
});

describe('defaultRetrievalPolicy', () => {
  it('returns retrieval from defaultPolicy', () => {
    const rp = defaultRetrievalPolicy();
    expect(rp).toBe(defaultPolicy.retrieval);
  });

  it('includes topology defaults under hybrid retrieval', () => {
    const topology = defaultPolicy.retrieval?.hybrid?.topology;
    expect(topology).toEqual(
      expect.objectContaining({
        enabled: true,
        mode: 'walk',
        seed_k: 6,
        max_hops: 2,
        hop_decay: 0.75,
        include_paths: true,
      })
    );
    expect(topology?.edge_policy).toEqual(
      expect.objectContaining({
        supports: expect.objectContaining({ weight: 0.9, direction: 'forward' }),
        extends: expect.objectContaining({ weight: 0.7, direction: 'forward' }),
        related: expect.objectContaining({ weight: 0.35, direction: 'both' }),
        contradicts: expect.objectContaining({ action: 'flag_conflict' }),
        supersedes: expect.objectContaining({ action: 'shadow_old' }),
      })
    );
  });
});

describe('defaultMaintenancePolicy', () => {
  it('returns maintenance from defaultPolicy', () => {
    const mp = defaultMaintenancePolicy();
    expect(mp).toBe(defaultPolicy.maintenance);
  });
});

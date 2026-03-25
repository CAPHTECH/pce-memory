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
});

describe('defaultMaintenancePolicy', () => {
  it('returns maintenance from defaultPolicy', () => {
    const mp = defaultMaintenancePolicy();
    expect(mp).toBe(defaultPolicy.maintenance);
  });
});

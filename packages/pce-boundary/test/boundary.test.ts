import { describe, it, expect } from 'vitest';
import { boundaryValidate } from '../src';
import { BoundaryPolicy } from '@pce/policy-schemas';

const policy: BoundaryPolicy = {
  version: '0.1',
  scopes: {
    session: { ttl: '1d' },
    project: { ttl: '30d' },
    principle: { ttl: 'inf' },
  },
  boundary_classes: {
    internal: { allow: ['*'], redact: ['email'] },
  },
};

describe('boundaryValidate', () => {
  it('redacts email with whitelist regex', () => {
    const res = boundaryValidate(
      { payload: 'Contact me at foo@example.com', allow: ['answer:task'], scope: 'project' },
      policy
    );
    expect(res.allowed).toBe(true);
    expect(res.redacted).toContain('[REDACTED]');
  });
});

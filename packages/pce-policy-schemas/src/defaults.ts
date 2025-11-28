import type { PolicyDocument } from './types.js';

export const defaultPolicy: PolicyDocument = {
  version: '0.1',
  boundary: {
    version: '0.1',
    scopes: {
      session: { ttl: '7d' },
      project: { ttl: '120d' },
      principle: { ttl: 'inf' },
    },
    boundary_classes: {
      public: { allow: ['*'] },
      internal: { allow: ['answer:task', 'tool:*'] },
      pii: {
        allow: ['tool:contact-lookup'],
        redact: ['email', 'phone'],
        escalation: 'human_review',
      },
      secret: { allow: [], escalation: 'deny' },
    },
  },
  retrieval: {
    hybrid: {
      alpha: 0.65,
      k_txt: 48,
      k_vec: 96,
      k_final: 12,
      recency_half_life_days: 30,
    },
  },
};

export function defaultBoundaryPolicy() {
  return defaultPolicy.boundary;
}

import type {
  BoundaryPolicy,
  MaintenancePolicy,
  PolicyDocument,
  RetrievalPolicy,
} from './types.js';

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
      threshold: 0.15,
      k_txt: 48,
      k_vec: 96,
      k_final: 12,
      recency_half_life_days: 30,
      mmr: {
        enabled: false,
        lambda: 0.72,
        max_candidates: 48,
      },
      query_expansion: {
        enabled: false,
        max_seed_entities: 3,
        max_related_entities: 8,
        max_expansion_terms: 6,
      },
      feedback_boost: {
        enabled: false,
        helpful_weight: 0.25,
        harmful_weight: 0.35,
        outdated_weight: 0.18,
        duplicate_weight: 0.12,
        min_multiplier: 0.45,
        max_multiplier: 1.65,
      },
      topology: {
        enabled: true,
        mode: 'walk',
        seed_k: 6,
        max_hops: 2,
        hop_decay: 0.75,
        include_paths: true,
        edge_policy: {
          supports: { weight: 0.9, direction: 'forward' },
          extends: { weight: 0.7, direction: 'forward' },
          related: { weight: 0.35, direction: 'both' },
          contradicts: { action: 'flag_conflict' },
          supersedes: { action: 'shadow_old' },
        },
      },
    },
  },
  maintenance: {
    hints_enabled: true,
    similarity_threshold: 0.9,
    stale_days: 30,
  },
};

export function defaultBoundaryPolicy(): BoundaryPolicy {
  return defaultPolicy.boundary;
}

export function defaultRetrievalPolicy(): RetrievalPolicy | undefined {
  return defaultPolicy.retrieval;
}

export function defaultMaintenancePolicy(): MaintenancePolicy | undefined {
  return defaultPolicy.maintenance;
}

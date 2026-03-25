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
    },
  },
  extraction: {
    llm_enabled: false,
    ollama_endpoint: 'http://127.0.0.1:11434',
    model: 'qwen3.5:9b',
  },
};

export function defaultBoundaryPolicy() {
  return defaultPolicy.boundary;
}

export function defaultRetrievalPolicy() {
  return defaultPolicy.retrieval;
}

export function defaultExtractionPolicy() {
  return defaultPolicy.extraction;
}

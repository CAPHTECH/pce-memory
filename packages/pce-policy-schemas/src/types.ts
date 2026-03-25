export type BoundaryClass = 'public' | 'internal' | 'pii' | 'secret' | string;

export interface BoundaryPolicy {
  version: string;
  scopes: {
    session: { ttl: string };
    project: { ttl: string };
    principle: { ttl: string };
  };
  boundary_classes: Record<
    BoundaryClass,
    {
      allow: string[];
      redact?: string[];
      escalation?: 'deny' | 'human_review' | string;
    }
  >;
}

export interface RetrievalPolicy {
  hybrid?: {
    alpha?: number;
    threshold?: number;
    k_txt?: number;
    k_vec?: number;
    k_final?: number;
    recency_half_life_days?: number;
    mmr?: {
      enabled?: boolean;
      lambda?: number;
      max_candidates?: number;
    };
    query_expansion?: {
      enabled?: boolean;
      max_seed_entities?: number;
      max_related_entities?: number;
      max_expansion_terms?: number;
    };
    feedback_boost?: {
      enabled?: boolean;
      helpful_weight?: number;
      harmful_weight?: number;
      outdated_weight?: number;
      duplicate_weight?: number;
      min_multiplier?: number;
      max_multiplier?: number;
    };
  };
}

export interface PolicyDocument {
  version: string;
  boundary: BoundaryPolicy;
  retrieval?: RetrievalPolicy;
}

export interface ValidationResult<T> {
  ok: boolean;
  value?: T;
  errors?: string[];
}

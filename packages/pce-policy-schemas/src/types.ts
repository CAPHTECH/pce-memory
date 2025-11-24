export type BoundaryClass = "public" | "internal" | "pii" | "secret" | string;

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
      escalation?: "deny" | "human_review" | string;
    }
  >;
}

export interface RetrievalPolicy {
  hybrid?: {
    alpha?: number;
    k_txt?: number;
    k_vec?: number;
    k_final?: number;
    recency_half_life_days?: number;
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

import type { MemoryType } from '../domain/types.js';

export interface PromotionQueueRow {
  id: string;
  source_layer: string;
  target_layer: string;
  source_ids: string;
  distilled_text: string;
  candidate_hash: string;
  proposed_kind: string;
  proposed_scope: string;
  proposed_boundary_class: string;
  proposed_memory_type?: MemoryType | null;
  provenance: string;
  evidence_ids: string;
  policy_version_checked?: string | null;
  boundary_check_result?: string | null;
  status: string;
  reviewers?: string | null;
  created_at: string;
  resolved_at?: string | null;
  accepted_claim_id?: string | null;
  rejected_reason?: string | null;
}

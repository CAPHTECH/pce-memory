/**
 * Shared helpers and types for integration-bugs test files.
 */
import { expect } from 'vitest';
import { getConnection } from '../../src/db/connection';
import { applyPolicy, dispatchTool, upsertClaimViaTool } from './retrievalPlannerTestUtils';

// Re-export for convenience
export { applyPolicy, dispatchTool, upsertClaimViaTool };

type ToolResponse = Awaited<ReturnType<typeof dispatchTool>>;
type ToolStructuredContent = NonNullable<ToolResponse['structuredContent']>;

export type ObserveResult = {
  observation_id: string;
  effective_boundary_class?: string;
};

export type DistillResult = {
  candidate_id: string;
  distilled_text: string;
  proposed_kind: string;
  proposed_scope: string;
  proposed_memory_type: string | null;
  proposed_boundary_class: string;
  status: string;
};

export type PromoteResult = {
  claim_id: string;
  is_new: boolean;
  promoted_from: string;
  rollback_token: string;
};

export type RollbackResult = {
  rollback_id: string;
  superseded_claim_id: string;
};

export type ActivateResult = {
  active_context_id: string;
  intent?: string;
  claims_count: number;
  claims: Array<{
    claim: {
      id: string;
      scope: string;
      boundary_class: string;
      kind: string;
      memory_type?: string | null;
      text?: string;
    };
    score: number;
    score_breakdown?: Record<string, unknown>;
    selection_reason?: string;
  }>;
  maintenance_hints?: {
    stale_claims?: Array<{ id: string }>;
    similar_pairs?: Array<{ claim_a_id: string; claim_b_id: string }>;
  };
  next_cursor?: string;
  has_more?: boolean;
};

export type FeedbackResult = {
  id: string;
  claim_id: string;
  signal: string;
};

export type LinkResult = {
  id: string;
  is_new: boolean;
  source_claim_id: string;
  target_claim_id: string;
  link_type: string;
  confidence: number;
};

export type SyncPushResult = {
  exported: { claims: number; entities?: number; relations?: number };
  target_dir: string;
  manifest_updated: boolean;
};

export type HealthResult = {
  total_claims: number;
  by_kind: Record<string, number>;
  by_scope: Record<string, number>;
};

export function expectSuccess<T extends ToolStructuredContent>(result: ToolResponse): T {
  if (result.isError) {
    const errorText = result.content?.[0]?.text ?? 'unknown error';
    const errorDetail = result.structuredContent?.error ?? {};
    throw new Error(`Expected success but got error: ${errorText} ${JSON.stringify(errorDetail)}`);
  }
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent as T;
}

export function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

export function buildProvenance(
  offsetMs: number,
  note?: string
): { at: string; actor: string; note?: string } {
  return note
    ? { at: isoOffset(offsetMs), actor: 'claude', note }
    : { at: isoOffset(offsetMs), actor: 'claude' };
}

export async function observeRaw(
  content: string,
  extra: Record<string, unknown> = {}
): Promise<ObserveResult> {
  return expectSuccess<ObserveResult>(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      extract: { mode: 'noop' },
      ...extra,
    })
  );
}

export async function distillFromObservations(
  observationIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: observationIds,
      ...extra,
    })
  );
}

export async function distillFromClaims(
  claimIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_claim_ids: claimIds,
      ...extra,
    })
  );
}

export async function promoteCandidate(
  candidateId: string,
  extra: Record<string, unknown> = {}
): Promise<PromoteResult> {
  return expectSuccess<PromoteResult>(
    await dispatchTool('pce_memory_promote', {
      candidate_id: candidateId,
      provenance: buildProvenance(-60_000),
      ...extra,
    })
  );
}

export async function rollbackClaim(claimId: string, reason: string): Promise<RollbackResult> {
  return expectSuccess<RollbackResult>(
    await dispatchTool('pce_memory_rollback', {
      claim_id: claimId,
      reason,
      provenance: buildProvenance(-30_000, reason),
    })
  );
}

export async function activateClaims(
  q: string,
  overrides: Record<string, unknown> = {}
): Promise<ActivateResult> {
  return expectSuccess<ActivateResult>(
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 10,
      q,
      ...overrides,
    })
  );
}

export async function submitFeedback(claimId: string, signal: string): Promise<FeedbackResult> {
  return expectSuccess<FeedbackResult>(
    await dispatchTool('pce_memory_feedback', {
      claim_id: claimId,
      signal,
    })
  );
}

export async function linkClaims(
  sourceClaimId: string,
  targetClaimId: string,
  linkType: string,
  confidence?: number
): Promise<LinkResult> {
  return expectSuccess<LinkResult>(
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: sourceClaimId,
      target_claim_id: targetClaimId,
      link_type: linkType,
      ...(confidence !== undefined ? { confidence } : {}),
    })
  );
}

export async function readClaimRow(claimId: string): Promise<
  | {
      scope: string;
      boundary_class: string;
      utility: number;
      confidence: number;
      tombstone: boolean;
      status: string;
      memory_type: string | null;
    }
  | undefined
> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT scope, boundary_class, utility, confidence, COALESCE(tombstone, FALSE) as tombstone, status, memory_type FROM claims WHERE id = $1',
    [claimId]
  );
  const rows = reader.getRowObjects() as Array<{
    scope: string;
    boundary_class: string;
    utility: number;
    confidence: number;
    tombstone: boolean;
    status: string;
    memory_type: string | null;
  }>;
  return rows[0];
}

export async function countClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM claims');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

export async function countActiveClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT COUNT(*) as cnt FROM claims c
     WHERE COALESCE(c.tombstone, FALSE) = FALSE
     AND NOT EXISTS (
       SELECT 1 FROM promotion_queue pq
       WHERE pq.accepted_claim_id = c.id AND pq.status = 'rolled_back'
     )`
  );
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

export async function countObservations(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM observations');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

export async function countPromotionQueue(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM promotion_queue');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

export async function countFeedback(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM feedback');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

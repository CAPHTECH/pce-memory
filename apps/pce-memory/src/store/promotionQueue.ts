import type { DuckDBConnection } from '@duckdb/node-api';
import { getConnection } from '../db/connection.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';
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

export interface InsertPromotionQueueInput {
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
  status?: string;
  reviewers?: string | null;
  created_at: string;
  resolved_at?: string | null;
  accepted_claim_id?: string | null;
  rejected_reason?: string | null;
}

const PROMOTION_QUEUE_COLUMNS =
  'id, source_layer, target_layer, source_ids, distilled_text, candidate_hash, proposed_kind, proposed_scope, proposed_boundary_class, proposed_memory_type, provenance, evidence_ids, policy_version_checked, boundary_check_result, status, reviewers, created_at, resolved_at, accepted_claim_id, rejected_reason';

function normalizePromotionRows(rows: PromotionQueueRow[]): PromotionQueueRow[] {
  return normalizeRowsTimestamps(rows) as PromotionQueueRow[];
}

export async function insertPromotionQueueRow(
  input: InsertPromotionQueueInput
): Promise<PromotionQueueRow> {
  const conn = await getConnection();
  await conn.run(
    `INSERT INTO promotion_queue (
      id, source_layer, target_layer, source_ids, distilled_text, candidate_hash,
      proposed_kind, proposed_scope, proposed_boundary_class, proposed_memory_type,
      provenance, evidence_ids, policy_version_checked, boundary_check_result, status, reviewers,
      created_at, resolved_at, accepted_claim_id, rejected_reason
    ) VALUES (
      $1, $2, $3, $4, $5, $6,
      $7, $8, $9, $10, $11, $12, $13, $14,
      $15, $16, $17, $18, $19, $20
    )`,
    [
      input.id,
      input.source_layer,
      input.target_layer,
      input.source_ids,
      input.distilled_text,
      input.candidate_hash,
      input.proposed_kind,
      input.proposed_scope,
      input.proposed_boundary_class,
      input.proposed_memory_type ?? null,
      input.provenance,
      input.evidence_ids,
      input.policy_version_checked ?? null,
      input.boundary_check_result ?? null,
      input.status ?? 'pending',
      input.reviewers ?? null,
      input.created_at,
      input.resolved_at ?? null,
      input.accepted_claim_id ?? null,
      input.rejected_reason ?? null,
    ]
  );

  const reader = await conn.runAndReadAll(
    `SELECT ${PROMOTION_QUEUE_COLUMNS} FROM promotion_queue WHERE id = $1`,
    [input.id]
  );
  const rawRows = reader.getRowObjects() as unknown as PromotionQueueRow[];
  return normalizePromotionRows(rawRows)[0]!;
}

export async function findPromotionQueueRowById(
  id: string
): Promise<PromotionQueueRow | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT ${PROMOTION_QUEUE_COLUMNS} FROM promotion_queue WHERE id = $1`,
    [id]
  );
  const rawRows = reader.getRowObjects() as unknown as PromotionQueueRow[];
  return normalizePromotionRows(rawRows)[0];
}

export async function findRollbackRecordByClaimId(
  claimId: string
): Promise<PromotionQueueRow | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT ${PROMOTION_QUEUE_COLUMNS}
     FROM promotion_queue
     WHERE accepted_claim_id = $1
       AND status = 'rolled_back'
     ORDER BY created_at DESC
     LIMIT 1`,
    [claimId]
  );
  const rawRows = reader.getRowObjects() as unknown as PromotionQueueRow[];
  return normalizePromotionRows(rawRows)[0];
}

export interface AcceptPromotionQueueInput {
  accepted_claim_id: string;
  reviewers?: string | null;
  resolved_at: string;
  provenance?: string;
}

export async function acceptPromotionQueueRow(
  id: string,
  input: AcceptPromotionQueueInput,
  connection?: DuckDBConnection
): Promise<boolean> {
  const conn = connection ?? (await getConnection());
  if (input.provenance !== undefined) {
    const reader = await conn.runAndReadAll(
      `UPDATE promotion_queue
       SET status = 'accepted',
           accepted_claim_id = $1,
           resolved_at = $2,
           reviewers = $3,
           provenance = $4
       WHERE id = $5
         AND status = 'pending'
       RETURNING id`,
      [input.accepted_claim_id, input.resolved_at, input.reviewers ?? null, input.provenance, id]
    );
    const rows = reader.getRowObjects() as Array<{ id: string }>;
    return rows.length > 0;
  }

  const reader = await conn.runAndReadAll(
    `UPDATE promotion_queue
     SET status = 'accepted',
         accepted_claim_id = $1,
         resolved_at = $2,
         reviewers = $3
     WHERE id = $4
       AND status = 'pending'
     RETURNING id`,
    [input.accepted_claim_id, input.resolved_at, input.reviewers ?? null, id]
  );
  const rows = reader.getRowObjects() as Array<{ id: string }>;
  return rows.length > 0;
}

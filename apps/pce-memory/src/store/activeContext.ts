import { getConnection } from '../db/connection.js';
import type { Claim } from './claims.js';
import { normalizeRowsTimestamps, safeJsonStringify } from '../utils/serialization.js';
import type { ScoreBreakdown } from './rerank.js';

export interface ActiveContext {
  id: string;
  claims: Claim[];
  intent?: string;
  expires_at?: Date | string | null;
  policy_version?: string;
}

export interface ActiveContextItemRow {
  id: string;
  active_context_id: string;
  claim_id: string;
  source_layer?: string | null;
  score?: number | null;
  score_breakdown?: string | null;
  selection_reason?: string | null;
  rank?: number | null;
}

export interface ActiveContextItemInput {
  id: string;
  active_context_id: string;
  claim_id: string;
  source_layer?: string;
  score?: number;
  score_breakdown?: ScoreBreakdown;
  selection_reason?: string;
  rank?: number;
}

export async function saveActiveContext(ac: ActiveContext): Promise<void> {
  const conn = await getConnection();
  // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
  await conn.run(
    'INSERT INTO active_contexts (id, claims, intent, expires_at, policy_version) VALUES ($1, $2, $3, $4, $5)',
    [
      ac.id,
      safeJsonStringify(ac.claims),
      ac.intent ?? null,
      ac.expires_at instanceof Date ? ac.expires_at.toISOString() : (ac.expires_at ?? null),
      ac.policy_version ?? null,
    ]
  );
}

export async function saveActiveContextItems(items: ActiveContextItemInput[]): Promise<void> {
  if (items.length === 0) {
    return;
  }

  const conn = await getConnection();
  for (const item of items) {
    await conn.run(
      `INSERT INTO active_context_items (
        id, active_context_id, claim_id, source_layer, score, score_breakdown, selection_reason, rank
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8)`,
      [
        item.id,
        item.active_context_id,
        item.claim_id,
        item.source_layer ?? null,
        item.score ?? null,
        item.score_breakdown ? safeJsonStringify(item.score_breakdown) : null,
        item.selection_reason ?? null,
        item.rank ?? null,
      ]
    );
  }
}

export async function findActiveContextById(id: string): Promise<ActiveContext | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, claims, intent, expires_at, policy_version FROM active_contexts WHERE id = $1',
    [id]
  );
  const rawRows = reader.getRowObjects() as Array<{
    id: string;
    claims: Claim[] | string;
    intent?: string | null;
    expires_at?: Date | string | null;
    policy_version?: string | null;
  }>;
  const rows = normalizeRowsTimestamps(rawRows);
  const row = rows[0];
  if (!row) {
    return undefined;
  }

  const claims =
    typeof row.claims === 'string'
      ? ((JSON.parse(row.claims) as Claim[]) ?? [])
      : ((row.claims as Claim[]) ?? []);

  return {
    id: row.id,
    claims,
    ...(row.intent !== null && row.intent !== undefined ? { intent: row.intent } : {}),
    ...(row.expires_at !== undefined ? { expires_at: row.expires_at ?? null } : {}),
    ...(row.policy_version !== null && row.policy_version !== undefined
      ? { policy_version: row.policy_version }
      : {}),
  };
}

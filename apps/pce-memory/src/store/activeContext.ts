import { getConnection } from '../db/connection.js';
import type { Claim } from './claims.js';
import { safeJsonStringify } from '../utils/serialization.js';

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

/**
 * Evidence Store（mcp-tools.md definitions.evidence準拠）
 * Claimの根拠情報
 */
import { getConnection } from "../db/connection.js";

/**
 * Evidence型（definitions.evidence準拠）
 */
export interface Evidence {
  id: string;
  claim_id: string;
  source_type?: string;
  source_id?: string;
  snippet?: string;
  at?: Date | string;
}

/**
 * Evidence入力型
 */
export type EvidenceInput = Omit<Evidence, "at"> & {
  at?: string;
};

/**
 * Evidenceを登録
 * Note: DBカラムはrecorded_at（DuckDB予約語回避）、APIはatを使用
 */
export async function insertEvidence(e: EvidenceInput): Promise<Evidence> {
  const conn = await getConnection();

  await conn.run(
    "INSERT INTO evidence (id, claim_id, source_type, source_id, snippet, recorded_at) VALUES ($1, $2, $3, $4, $5, COALESCE($6::TIMESTAMP, CURRENT_TIMESTAMP))",
    [e.id, e.claim_id, e.source_type ?? null, e.source_id ?? null, e.snippet ?? null, e.at ?? null]
  );

  const reader = await conn.runAndReadAll(
    "SELECT id, claim_id, source_type, source_id, snippet, recorded_at AS at FROM evidence WHERE id = $1",
    [e.id]
  );
  return (reader.getRowObjects() as unknown as Evidence[])[0]!;
}

/**
 * Claimに関連するEvidenceを取得
 */
export async function getEvidenceForClaim(claimId: string): Promise<Evidence[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, claim_id, source_type, source_id, snippet, recorded_at AS at FROM evidence WHERE claim_id = $1 ORDER BY recorded_at DESC",
    [claimId]
  );
  return reader.getRowObjects() as unknown as Evidence[];
}

/**
 * 複数ClaimのEvidenceを一括取得（バッチ用）
 */
export async function getEvidenceForClaims(claimIds: string[]): Promise<Map<string, Evidence[]>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, i) => `$${i + 1}`).join(",");

  const reader = await conn.runAndReadAll(
    `SELECT id, claim_id, source_type, source_id, snippet, recorded_at AS at
     FROM evidence
     WHERE claim_id IN (${placeholders})
     ORDER BY claim_id, recorded_at DESC`,
    claimIds
  );

  const rows = reader.getRowObjects() as unknown as Evidence[];
  const result = new Map<string, Evidence[]>();

  for (const row of rows) {
    const existing = result.get(row.claim_id) ?? [];
    existing.push(row);
    result.set(row.claim_id, existing);
  }

  return result;
}

/**
 * source_typeで検索
 */
export async function findEvidenceBySourceType(sourceType: string, limit: number = 100): Promise<Evidence[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, claim_id, source_type, source_id, snippet, recorded_at AS at FROM evidence WHERE source_type = $1 LIMIT $2",
    [sourceType, limit]
  );
  return reader.getRowObjects() as unknown as Evidence[];
}

/**
 * Relation Store（mcp-tools.md definitions.relation準拠）
 * Graph Memory: Entity間の関係
 */
import { getConnection } from "../db/connection.js";

/**
 * Relation型（definitions.relation準拠）
 */
export interface Relation {
  id: string;
  src_id: string;
  dst_id: string;
  type: string;
  props?: Record<string, unknown>;
  evidence_claim_id?: string;
  created_at?: Date | string;
}

/**
 * Relation入力型
 */
export type RelationInput = Omit<Relation, "created_at">;

/**
 * Relationを登録（idempotent upsert）
 */
export async function upsertRelation(r: RelationInput): Promise<Relation> {
  const conn = await getConnection();

  // 既存チェック
  const existing = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE id = $1",
    [r.id]
  );
  const rows = existing.getRowObjects() as unknown as Relation[];
  if (rows.length > 0 && rows[0]) {
    return rows[0];
  }

  // 新規挿入
  const propsJson = r.props ? JSON.stringify(r.props) : null;
  await conn.run(
    "INSERT INTO relations (id, src_id, dst_id, type, props, evidence_claim_id) VALUES ($1, $2, $3, $4, $5, $6)",
    [r.id, r.src_id, r.dst_id, r.type, propsJson, r.evidence_claim_id ?? null]
  );

  const inserted = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE id = $1",
    [r.id]
  );
  return (inserted.getRowObjects() as unknown as Relation[])[0]!;
}

/**
 * Entityから発する関係を取得
 */
export async function getRelationsFromEntity(entityId: string): Promise<Relation[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE src_id = $1",
    [entityId]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * Entityに向かう関係を取得
 */
export async function getRelationsToEntity(entityId: string): Promise<Relation[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE dst_id = $1",
    [entityId]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * Claimをevidenceとする関係を取得
 */
export async function getRelationsByEvidence(claimId: string): Promise<Relation[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE evidence_claim_id = $1",
    [claimId]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * 関係タイプで検索
 */
export async function findRelationsByType(type: string, limit: number = 100): Promise<Relation[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE type = $1 LIMIT $2",
    [type, limit]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * Relation Store（mcp-tools.md definitions.relation準拠）
 * Graph Memory: Entity間の関係
 */
import { getConnection } from '../db/connection.js';

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
export type RelationInput = Omit<Relation, 'created_at'>;

/**
 * Relationを登録（idempotent upsert）
 */
export async function upsertRelation(r: RelationInput): Promise<Relation> {
  const conn = await getConnection();

  // 既存チェック
  const existing = await conn.runAndReadAll(
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE id = $1',
    [r.id]
  );
  const rows = existing.getRowObjects() as unknown as Relation[];
  if (rows.length > 0 && rows[0]) {
    return rows[0];
  }

  // 新規挿入
  const propsJson = r.props ? JSON.stringify(r.props) : null;
  await conn.run(
    'INSERT INTO relations (id, src_id, dst_id, type, props, evidence_claim_id) VALUES ($1, $2, $3, $4, $5, $6)',
    [r.id, r.src_id, r.dst_id, r.type, propsJson, r.evidence_claim_id ?? null]
  );

  const inserted = await conn.runAndReadAll(
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE id = $1',
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
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE src_id = $1',
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
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE dst_id = $1',
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
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE evidence_claim_id = $1',
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
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE type = $1 LIMIT $2',
    [type, limit]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * IDでRelationを取得
 */
export async function findRelationById(id: string): Promise<Relation | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations WHERE id = $1',
    [id]
  );
  const rows = reader.getRowObjects() as unknown as Relation[];
  return rows[0];
}

/**
 * 全Relationを取得（同期機能用）
 *
 * @param limit 取得上限（デフォルト10000）
 * @returns Relation配列
 */
export async function listAllRelations(limit: number = 10000): Promise<Relation[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations ORDER BY created_at DESC LIMIT $1',
    [limit]
  );
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * Relationフィルターオプション（Phase 2: 増分同期用）
 */
export interface RelationFilterOptions {
  since?: Date;
  limit?: number;
}

/**
 * フィルターに基づいてRelationを取得（増分同期用）
 *
 * @param options フィルターオプション
 * @returns Relation配列
 */
export async function listRelationsByFilter(options: RelationFilterOptions = {}): Promise<Relation[]> {
  const conn = await getConnection();
  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  if (options.since) {
    conditions.push(`created_at >= $${paramIndex}`);
    params.push(options.since.toISOString());
    paramIndex++;
  }

  let sql = 'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations';
  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }
  sql += ` ORDER BY created_at DESC`;

  const limit = options.limit ?? 10000;
  sql += ` LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  return reader.getRowObjects() as unknown as Relation[];
}

/**
 * Relationクエリフィルター型
 */
export interface RelationQueryFilters {
  id?: string;
  src_id?: string;
  dst_id?: string;
  type?: string;
  evidence_claim_id?: string;
  limit?: number;
}

/**
 * フィルターに基づいてRelationを検索（AND論理）
 * 少なくとも1つのフィルターが必要
 */
export async function queryRelations(filters: RelationQueryFilters): Promise<Relation[]> {
  const conn = await getConnection();
  const limit = Math.min(filters.limit ?? 50, 100);

  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  if (filters.id !== undefined) {
    conditions.push(`id = $${paramIndex++}`);
    params.push(filters.id);
  }

  if (filters.src_id !== undefined) {
    conditions.push(`src_id = $${paramIndex++}`);
    params.push(filters.src_id);
  }

  if (filters.dst_id !== undefined) {
    conditions.push(`dst_id = $${paramIndex++}`);
    params.push(filters.dst_id);
  }

  if (filters.type !== undefined) {
    conditions.push(`type = $${paramIndex++}`);
    params.push(filters.type);
  }

  if (filters.evidence_claim_id !== undefined) {
    conditions.push(`evidence_claim_id = $${paramIndex++}`);
    params.push(filters.evidence_claim_id);
  }

  // クエリ構築
  let sql = 'SELECT id, src_id, dst_id, type, props, evidence_claim_id, created_at FROM relations';

  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }

  sql += ` ORDER BY created_at DESC LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  return reader.getRowObjects() as unknown as Relation[];
}

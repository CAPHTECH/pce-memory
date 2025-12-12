/**
 * Entity Store（mcp-tools.md definitions.entity準拠）
 * Graph Memory: Actor, Artifact, Event, Concept
 */
import { getConnection } from '../db/connection.js';

/**
 * Entity型（definitions.entity準拠）
 */
export interface Entity {
  id: string;
  type: 'Actor' | 'Artifact' | 'Event' | 'Concept';
  name: string;
  canonical_key?: string;
  attrs?: Record<string, unknown>;
  created_at?: Date | string;
}

/**
 * Entity入力型
 */
export type EntityInput = Omit<Entity, 'created_at'>;

/**
 * Entityを登録（idempotent upsert）
 */
export async function upsertEntity(e: EntityInput): Promise<Entity> {
  const conn = await getConnection();

  // 既存チェック
  const existing = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE id = $1',
    [e.id]
  );
  const rows = existing.getRowObjects() as unknown as Entity[];
  if (rows.length > 0 && rows[0]) {
    return rows[0];
  }

  // 新規挿入
  const attrsJson = e.attrs ? JSON.stringify(e.attrs) : null;
  await conn.run(
    'INSERT INTO entities (id, type, name, canonical_key, attrs) VALUES ($1, $2, $3, $4, $5)',
    [e.id, e.type, e.name, e.canonical_key ?? null, attrsJson]
  );

  const inserted = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE id = $1',
    [e.id]
  );
  return (inserted.getRowObjects() as unknown as Entity[])[0]!;
}

/**
 * Claim-Entity関連を登録
 */
export async function linkClaimEntity(claimId: string, entityId: string): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    'INSERT INTO claim_entities (claim_id, entity_id) VALUES ($1, $2) ON CONFLICT DO NOTHING',
    [claimId, entityId]
  );
}

/**
 * Claimに関連するEntitiesを取得
 */
export async function getEntitiesForClaim(claimId: string): Promise<Entity[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT e.id, e.type, e.name, e.canonical_key, e.attrs, e.created_at
     FROM entities e
     INNER JOIN claim_entities ce ON ce.entity_id = e.id
     WHERE ce.claim_id = $1`,
    [claimId]
  );
  return reader.getRowObjects() as unknown as Entity[];
}

/**
 * Entityを検索（type指定）
 */
export async function findEntitiesByType(
  type: Entity['type'],
  limit: number = 100
): Promise<Entity[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE type = $1 LIMIT $2',
    [type, limit]
  );
  return reader.getRowObjects() as unknown as Entity[];
}

/**
 * canonical_keyでEntityを検索
 */
export async function findEntityByCanonicalKey(canonicalKey: string): Promise<Entity | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE canonical_key = $1',
    [canonicalKey]
  );
  const rows = reader.getRowObjects() as unknown as Entity[];
  return rows[0];
}

/**
 * IDでEntityを取得
 */
export async function findEntityById(id: string): Promise<Entity | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE id = $1',
    [id]
  );
  const rows = reader.getRowObjects() as unknown as Entity[];
  return rows[0];
}

/**
 * 全Entityを取得（同期機能用）
 *
 * @param limit 取得上限（デフォルト10000）
 * @returns Entity配列
 */
export async function listAllEntities(limit: number = 10000): Promise<Entity[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities ORDER BY created_at DESC LIMIT $1',
    [limit]
  );
  return reader.getRowObjects() as unknown as Entity[];
}

/**
 * Entityクエリフィルター型
 */
export interface EntityQueryFilters {
  id?: string;
  type?: Entity['type'];
  canonical_key?: string;
  claim_id?: string;
  limit?: number;
}

/**
 * フィルターに基づいてEntityを検索（AND論理）
 * 少なくとも1つのフィルターが必要
 */
export async function queryEntities(filters: EntityQueryFilters): Promise<Entity[]> {
  const conn = await getConnection();
  const limit = Math.min(filters.limit ?? 50, 100);

  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  // claim_idの場合はJOINが必要
  const needsJoin = filters.claim_id !== undefined;

  if (filters.id !== undefined) {
    conditions.push(`e.id = $${paramIndex++}`);
    params.push(filters.id);
  }

  if (filters.type !== undefined) {
    conditions.push(`e.type = $${paramIndex++}`);
    params.push(filters.type);
  }

  if (filters.canonical_key !== undefined) {
    conditions.push(`e.canonical_key = $${paramIndex++}`);
    params.push(filters.canonical_key);
  }

  if (filters.claim_id !== undefined) {
    conditions.push(`ce.claim_id = $${paramIndex++}`);
    params.push(filters.claim_id);
  }

  // クエリ構築
  let sql: string;
  if (needsJoin) {
    sql = `SELECT e.id, e.type, e.name, e.canonical_key, e.attrs, e.created_at
           FROM entities e
           INNER JOIN claim_entities ce ON ce.entity_id = e.id`;
  } else {
    sql = `SELECT e.id, e.type, e.name, e.canonical_key, e.attrs, e.created_at FROM entities e`;
  }

  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }

  sql += ` ORDER BY e.created_at DESC LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  return reader.getRowObjects() as unknown as Entity[];
}

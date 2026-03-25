/**
 * Entity Store（mcp-tools.md definitions.entity準拠）
 * Graph Memory: Actor, Artifact, Event, Concept
 */
import { getConnection } from '../db/connection.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';

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
 * DBから取得したEntityのattrsフィールドをパース
 * DuckDBはJSON列を文字列として返すため、オブジェクトに変換する
 */
function parseEntityAttrs(entity: Entity): Entity {
  if (entity.attrs && typeof entity.attrs === 'string') {
    try {
      return { ...entity, attrs: JSON.parse(entity.attrs as string) as Record<string, unknown> };
    } catch (e: unknown) {
      console.warn(`[pce-memory] Failed to parse entity attrs for ${entity.id}:`, e);
      return entity;
    }
  }
  return entity;
}

/**
 * 複数のEntityのattrsをパースしタイムスタンプを正規化
 */
function normalizeEntityRows(rawRows: Entity[]): Entity[] {
  return normalizeRowsTimestamps(rawRows).map(parseEntityAttrs);
}

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
  const rawRows = existing.getRowObjects() as unknown as Entity[];
  const rows = normalizeEntityRows(rawRows);
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
  return normalizeEntityRows(inserted.getRowObjects() as unknown as Entity[])[0]!;
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
  return normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
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
  return normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
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
  const rows = normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
  return rows[0];
}

/**
 * 名前でEntityを検索（大文字小文字を無視）
 */
export async function findEntityByName(name: string): Promise<Entity | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, type, name, canonical_key, attrs, created_at FROM entities WHERE LOWER(name) = LOWER($1) ORDER BY created_at DESC LIMIT 1',
    [name]
  );
  const rows = normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
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
  const rows = normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
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
  return normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
}

/**
 * Entityフィルターオプション（Phase 2: 増分同期用）
 */
export interface EntityFilterOptions {
  since?: Date;
  limit?: number;
}

/**
 * フィルターに基づいてEntityを取得（増分同期用）
 *
 * @param options フィルターオプション
 * @returns Entity配列
 */
export async function listEntitiesByFilter(options: EntityFilterOptions = {}): Promise<Entity[]> {
  const conn = await getConnection();
  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  if (options.since) {
    conditions.push(`created_at >= $${paramIndex}`);
    params.push(options.since.toISOString());
    paramIndex++;
  }

  let sql = 'SELECT id, type, name, canonical_key, attrs, created_at FROM entities';
  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }
  sql += ` ORDER BY created_at DESC`;

  const limit = options.limit ?? 10000;
  sql += ` LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  return normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
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
  const rawLimit = filters.limit ?? 50;
  const limit = Number.isFinite(rawLimit) && rawLimit > 0 ? Math.min(Math.floor(rawLimit), 100) : 50;

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
  return normalizeEntityRows(reader.getRowObjects() as unknown as Entity[]);
}

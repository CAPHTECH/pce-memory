import type { DuckDBConnection } from '@duckdb/node-api';
import { getConnection, withDedicatedConnection, withWriteConnection } from '../db/connection.js';
import type { EmbeddingService, SensitivityLevel } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { saveClaimVector, splitQueryWords, buildWordOrCondition } from './hybridSearch.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';
import type { ClaimStatus, MemoryType } from '../domain/types.js';
import { isValidClaimStatus } from '../domain/types.js';

export const WORKING_STATE_STALE_AFTER_DAYS = 14;

function activeClaimFilter(alias: string): string {
  return `COALESCE(${alias}.tombstone, FALSE) = FALSE
    AND NOT ${rollbackRecordExistsFilter(alias)}`;
}

function rollbackRecordExistsFilter(alias: string): string {
  return `EXISTS (
      SELECT 1
      FROM promotion_queue pq
      WHERE pq.accepted_claim_id = ${alias}.id
        AND pq.status = 'rolled_back'
    )`;
}

/**
 * Provenance: 由来情報（mcp-tools.md §1.y準拠）
 */
export interface Provenance {
  at: string; // ISO8601 datetime (required)
  actor?: string;
  git?: {
    commit?: string;
    repo?: string;
    url?: string;
    files?: string[];
  };
  url?: string;
  note?: string;
  signed?: boolean;
}

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  memory_type?: MemoryType | null;
  status: ClaimStatus;
  content_hash: string;
  // g()再ランキング用フィールド（ADR-0004準拠）
  utility: number;
  confidence: number;
  created_at: Date | string;
  updated_at: Date | string;
  // recency計算の基準時刻（positive feedbackでのみ更新）
  recency_anchor: Date | string;
  retrieval_count: number;
  last_retrieved_at?: Date | string | null;
  tombstone?: boolean;
  tombstone_at?: Date | string | null;
  rollback_reason?: string | null;
  superseded_by?: string | null;
  has_rollback_record?: boolean;
  // 由来情報（mcp-tools.md §1.y準拠）
  provenance?: Provenance;
}

export interface ClaimRow extends Omit<Claim, 'provenance' | 'has_rollback_record' | 'status'> {
  status?: ClaimStatus | string | null;
  provenance?: Provenance | string | null;
  has_rollback_record?: unknown;
}

/**
 * upsertClaimの戻り値型
 * isNew: 新規挿入された場合はtrue、既存レコードを返した場合はfalse
 */
export interface UpsertResult {
  claim: Claim;
  isNew: boolean;
}

/**
 * ContentHashCollisionError: content_hashが一致するがテキストが異なる場合のエラー
 * DomainErrorインターフェースに準拠しつつ、Errorを継承してthrow/catchに対応
 */
export class ContentHashCollisionError extends Error {
  readonly _tag = 'DomainError' as const;
  readonly code = 'CONTENT_HASH_COLLISION' as const;
  constructor() {
    super('content_hash collision: existing claim text differs for identical content_hash');
    this.name = 'ContentHashCollisionError';
  }
}

/**
 * Claimを登録（idempotent upsert）
 * 既存のcontent_hashがある場合は既存レコードを返す（isNew: false）
 * 新規の場合は挿入して返す（isNew: true）
 */
/** g()再ランキング用フィールドを含むClaim入力型 */
export type ClaimInput = Omit<
  Claim,
  | 'id'
  | 'memory_type'
  | 'status'
  | 'utility'
  | 'confidence'
  | 'created_at'
  | 'updated_at'
  | 'recency_anchor'
  | 'retrieval_count'
  | 'last_retrieved_at'
> & {
  memory_type?: MemoryType;
  status?: ClaimStatus;
  provenance?: Provenance;
};

/** 全カラムのSELECT句 */
const CLAIM_COLUMNS =
  'id, text, kind, scope, boundary_class, memory_type, status, content_hash, utility, confidence, created_at, updated_at, recency_anchor, retrieval_count, last_retrieved_at, provenance, tombstone, tombstone_at, rollback_reason, superseded_by';

/**
 * DBから取得したClaimのprovenanceフィールドをパース
 * DuckDBはJSON列を文字列として返すため、オブジェクトに変換する
 *
 * exactOptionalPropertyTypes対応: undefinedを代入せずプロパティを省略する
 */
function parseClaimProvenance(claim: ClaimRow): Claim {
  const normalizedClaim: Claim = {
    id: claim.id,
    text: claim.text,
    kind: claim.kind,
    scope: claim.scope,
    boundary_class: claim.boundary_class,
    memory_type: claim.memory_type ?? null,
    status: isValidClaimStatus(claim.status) ? claim.status : 'active',
    content_hash: claim.content_hash,
    utility: claim.utility,
    confidence: claim.confidence,
    created_at: claim.created_at,
    updated_at: claim.updated_at,
    recency_anchor: claim.recency_anchor,
    retrieval_count:
      typeof claim.retrieval_count === 'number' && Number.isFinite(claim.retrieval_count)
        ? claim.retrieval_count
        : 0,
    last_retrieved_at: claim.last_retrieved_at ?? null,
    tombstone: Boolean(claim.tombstone),
    tombstone_at: claim.tombstone_at ?? null,
    rollback_reason: claim.rollback_reason ?? null,
    superseded_by: claim.superseded_by ?? null,
  };

  if (claim.has_rollback_record !== undefined && claim.has_rollback_record !== null) {
    normalizedClaim.has_rollback_record = Boolean(claim.has_rollback_record);
  }

  if (claim.provenance && typeof claim.provenance === 'string') {
    try {
      return { ...normalizedClaim, provenance: JSON.parse(claim.provenance) as Provenance };
    } catch (e: unknown) {
      console.warn(`[pce-memory] Failed to parse claim provenance for ${claim.id}:`, e);
      return normalizedClaim;
    }
  }
  if (claim.provenance && typeof claim.provenance === 'object') {
    return { ...normalizedClaim, provenance: claim.provenance };
  }
  return normalizedClaim;
}

/**
 * 複数のClaimのprovenanceをパース
 */
function parseClaimsProvenance(claims: ClaimRow[]): Claim[] {
  return claims.map((claim) => parseClaimProvenance(claim));
}

async function withClaimWriteConnection<T>(
  connection: DuckDBConnection | undefined,
  operation: (conn: DuckDBConnection) => Promise<T>
): Promise<T> {
  if (connection) {
    return operation(connection);
  }
  return withWriteConnection(operation);
}

export async function upsertClaim(
  c: ClaimInput,
  connection?: DuckDBConnection
): Promise<UpsertResult> {
  return withClaimWriteConnection(connection, async (conn) => {
    try {
      const reader = await conn.runAndReadAll(
        `SELECT ${CLAIM_COLUMNS} FROM claims c WHERE c.content_hash = $1 AND ${activeClaimFilter('c')}`,
        [c.content_hash]
      );
      const rawExisting = reader.getRowObjects() as unknown as ClaimRow[];
      const existing = parseClaimsProvenance(normalizeRowsTimestamps(rawExisting));
      if (existing.length > 0 && existing[0]) {
        if (existing[0].text !== c.text) {
          throw new ContentHashCollisionError();
        }
        return { claim: existing[0], isNew: false };
      }

      const rolledBackReader = await conn.runAndReadAll(
        `SELECT ${CLAIM_COLUMNS} FROM claims c WHERE c.content_hash = $1
         AND (COALESCE(c.tombstone, FALSE) = TRUE OR ${rollbackRecordExistsFilter('c')})`,
        [c.content_hash]
      );
      const rawRolledBack = rolledBackReader.getRowObjects() as unknown as ClaimRow[];
      const rolledBack = parseClaimsProvenance(normalizeRowsTimestamps(rawRolledBack));
      if (rolledBack.length > 0 && rolledBack[0]) {
        const revived = rolledBack[0];
        const provenanceJson = c.provenance ? JSON.stringify(c.provenance) : null;
        const memoryType = c.memory_type ?? null;
        const status = c.status ?? 'active';
        await conn.run(
          `UPDATE claims
           SET tombstone = FALSE,
               tombstone_at = NULL,
               rollback_reason = NULL,
               superseded_by = NULL,
               kind = $1,
               scope = $2,
               boundary_class = $3,
               memory_type = $4,
               status = $5,
               provenance = $6,
               updated_at = CURRENT_TIMESTAMP
           WHERE id = $7`,
          [c.kind, c.scope, c.boundary_class, memoryType, status, provenanceJson, revived.id]
        );
        await conn.run(
          `DELETE FROM promotion_queue WHERE accepted_claim_id = $1 AND status = 'rolled_back'`,
          [revived.id]
        );
        const revivedReader = await conn.runAndReadAll(
          `SELECT ${CLAIM_COLUMNS} FROM claims WHERE id = $1`,
          [revived.id]
        );
        const rawRevived = revivedReader.getRowObjects() as unknown as ClaimRow[];
        const parsed = parseClaimsProvenance(normalizeRowsTimestamps(rawRevived));
        return { claim: parsed[0]!, isNew: true };
      }

      const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
      const provenanceJson = c.provenance ? JSON.stringify(c.provenance) : null;
      const memoryType = c.memory_type ?? null;
      const status = c.status ?? 'active';
      await conn.run(
        'INSERT INTO claims (id, text, kind, scope, boundary_class, memory_type, status, content_hash, provenance) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)',
        [
          id,
          c.text,
          c.kind,
          c.scope,
          c.boundary_class,
          memoryType,
          status,
          c.content_hash,
          provenanceJson,
        ]
      );
      const insertedReader = await conn.runAndReadAll(
        `SELECT ${CLAIM_COLUMNS} FROM claims WHERE id = $1`,
        [id]
      );
      const rawInserted = insertedReader.getRowObjects() as unknown as ClaimRow[];
      const inserted = parseClaimsProvenance(normalizeRowsTimestamps(rawInserted));
      return { claim: inserted[0]!, isNew: true };
    } catch (e: unknown) {
      const reader = await conn.runAndReadAll(
        `SELECT ${CLAIM_COLUMNS} FROM claims c WHERE c.content_hash = $1 AND ${activeClaimFilter('c')}`,
        [c.content_hash]
      );
      const rawExisting = reader.getRowObjects() as unknown as ClaimRow[];
      const existing = parseClaimsProvenance(normalizeRowsTimestamps(rawExisting));
      if (existing.length > 0 && existing[0]) {
        if (existing[0].text !== c.text) {
          throw new ContentHashCollisionError();
        }
        return { claim: existing[0], isNew: false };
      }
      throw e;
    }
  });
}

/**
 * スコープ別Claim一覧取得（単語分割OR検索対応）
 *
 * 検索クエリは空白（半角・全角）で分割され、各単語のいずれかを含むClaimがマッチ。
 * 例: "状態管理 XState Valtio" → "状態管理" OR "XState" OR "Valtio"
 *
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @param q 検索クエリ（オプション、空白区切りで複数単語指定可能）
 * @returns Claim配列
 */
export async function listClaimsByScope(
  scopes: string[],
  limit: number,
  q?: string
): Promise<Claim[]> {
  const conn = await getConnection();

  // DuckDBはプレースホルダーのIN句に配列をそのまま渡せないため、動的にSQL構築
  const placeholders = scopes.map((_, i) => `$${i + 1}`).join(',');

  // クエリを単語に分割
  const words = q ? splitQueryWords(q) : [];

  // 空クエリの場合はスコープ内の全Claimを返す
  if (words.length === 0) {
    const sql = `SELECT ${CLAIM_COLUMNS},
              coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders})
         AND ${activeClaimFilter('c')}
       ORDER BY score DESC
       LIMIT $${scopes.length + 1}`;
    const reader = await conn.runAndReadAll(sql, [...scopes, limit]);
    const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
    return parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  }

  // 単語OR条件を構築
  const { sql: wordCondition, params: wordParams } = buildWordOrCondition(words, scopes.length + 1);

  const sql = `SELECT ${CLAIM_COLUMNS},
              coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders}) AND ${activeClaimFilter('c')} AND ${wordCondition}
       ORDER BY score DESC
       LIMIT $${scopes.length + wordParams.length + 1}`;

  const reader = await conn.runAndReadAll(sql, [...scopes, ...wordParams, limit]);
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  return parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
}

export async function findClaimById(id: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(`SELECT ${CLAIM_COLUMNS} FROM claims WHERE id = $1`, [
    id,
  ]);
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  const rows = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  return rows[0];
}

/**
 * content_hashでClaimを検索
 */
export async function findClaimByContentHash(contentHash: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT ${CLAIM_COLUMNS} FROM claims c WHERE c.content_hash = $1 AND ${activeClaimFilter('c')}`,
    [contentHash]
  );
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  const rows = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  return rows[0];
}

export interface FindClaimByContentHashAnyStateOptions {
  includeRollbackMetadata?: boolean;
}

export async function findClaimByContentHashAnyState(
  contentHash: string,
  options: FindClaimByContentHashAnyStateOptions = {}
): Promise<Claim | undefined> {
  const conn = await getConnection();
  const selectColumns = options.includeRollbackMetadata
    ? `${CLAIM_COLUMNS}, ${rollbackRecordExistsFilter('c')} AS has_rollback_record`
    : CLAIM_COLUMNS;
  const reader = await conn.runAndReadAll(
    `SELECT ${selectColumns}
     FROM claims c
     WHERE c.content_hash = $1`,
    [contentHash]
  );
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  const rows = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  return rows[0];
}

/**
 * フィルター条件によるClaim一覧取得（同期機能用）
 *
 * @param options フィルターオプション
 * @returns Claim配列
 */
export interface ClaimFilterOptions {
  scopes?: string[];
  boundaryClasses?: string[];
  since?: Date;
  limit?: number;
  includeInactive?: boolean;
  includeRollbackMetadata?: boolean;
}

export async function listClaimsByFilter(options: ClaimFilterOptions): Promise<Claim[]> {
  const conn = await getConnection();
  const selectColumns = options.includeRollbackMetadata
    ? `${CLAIM_COLUMNS}, ${rollbackRecordExistsFilter('c')} AS has_rollback_record`
    : CLAIM_COLUMNS;
  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  if (!options.includeInactive) {
    conditions.push(activeClaimFilter('c'));
  }

  // スコープフィルター
  if (options.scopes && options.scopes.length > 0) {
    const placeholders = options.scopes.map((_, i) => `$${paramIndex + i}`).join(',');
    conditions.push(`c.scope IN (${placeholders})`);
    params.push(...options.scopes);
    paramIndex += options.scopes.length;
  }

  // 境界クラスフィルター
  if (options.boundaryClasses && options.boundaryClasses.length > 0) {
    const placeholders = options.boundaryClasses.map((_, i) => `$${paramIndex + i}`).join(',');
    conditions.push(`c.boundary_class IN (${placeholders})`);
    params.push(...options.boundaryClasses);
    paramIndex += options.boundaryClasses.length;
  }

  // 日時フィルター（増分エクスポート用）
  if (options.since) {
    conditions.push(`c.created_at >= $${paramIndex}`);
    params.push(options.since.toISOString());
    paramIndex++;
  }

  // クエリ構築
  let sql = `SELECT ${selectColumns} FROM claims c`;
  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }
  sql += ` ORDER BY created_at DESC`;

  // リミット
  const limit = options.limit ?? 10000;
  sql += ` LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  return parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
}

/**
 * Claimのboundary_classを更新（同期時のマージ用）
 *
 * @param id Claim ID
 * @param boundaryClass 新しいboundary_class
 */
export async function updateClaimBoundaryClass(id: string, boundaryClass: string): Promise<void> {
  await withWriteConnection(async (conn) => {
    await conn.run(
      'UPDATE claims SET boundary_class = $1, updated_at = CURRENT_TIMESTAMP WHERE id = $2',
      [boundaryClass, id]
    );
  });
}

export interface UpdateClaimSyncMetadataInput {
  boundaryClass?: string;
  memoryType?: MemoryType;
}

export async function updateClaimSyncMetadata(
  id: string,
  input: UpdateClaimSyncMetadataInput
): Promise<void> {
  const assignments: string[] = [];
  const values: Array<string> = [];

  if (input.boundaryClass !== undefined) {
    assignments.push(`boundary_class = $${values.length + 1}`);
    values.push(input.boundaryClass);
  }

  if (input.memoryType !== undefined) {
    assignments.push(`memory_type = $${values.length + 1}`);
    values.push(input.memoryType);
  }

  if (assignments.length === 0) {
    return;
  }

  assignments.push('updated_at = CURRENT_TIMESTAMP');
  await withWriteConnection(async (conn) => {
    await conn.run(
      `UPDATE claims SET ${assignments.join(', ')} WHERE id = $${values.length + 1}`,
      [...values, id]
    );
  });
}

async function feedbackTableExists(): Promise<boolean> {
  return withDedicatedConnection(async (conn) => {
    const reader = await conn.runAndReadAll(
      "SELECT COUNT(*)::INTEGER AS cnt FROM information_schema.tables WHERE table_name = 'feedback'"
    );
    const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
    return Number(rows[0]?.cnt ?? 0) > 0;
  });
}

function resolveStaleAfterDays(staleAfterDays: number | undefined): number {
  return typeof staleAfterDays === 'number' && Number.isFinite(staleAfterDays) && staleAfterDays > 0
    ? Math.floor(staleAfterDays)
    : WORKING_STATE_STALE_AFTER_DAYS;
}

export async function updateClaimStatus(id: string, status: ClaimStatus): Promise<void> {
  await withWriteConnection(async (conn) => {
    await conn.run(
      'UPDATE claims SET status = $1, updated_at = CURRENT_TIMESTAMP WHERE id = $2',
      [status, id]
    );
  });
}

export async function recordClaimRetrievals(
  ids: string[],
  retrievedAt: string = new Date().toISOString()
): Promise<void> {
  const uniqueIds = [...new Set(ids.filter((id) => id.length > 0))];
  if (uniqueIds.length === 0) {
    return;
  }

  const placeholders = uniqueIds.map((_, index) => `$${index + 2}`).join(',');
  await withWriteConnection(async (conn) => {
    await conn.run(
      `UPDATE claims
       SET retrieval_count = COALESCE(retrieval_count, 0) + 1,
           last_retrieved_at = $1
       WHERE id IN (${placeholders})`,
      [retrievedAt, ...uniqueIds]
    );
  });
}

export async function markStaleWorkingStateClaims(
  options: {
    staleAfterDays?: number;
  } = {}
): Promise<string[]> {
  const staleAfterDays = resolveStaleAfterDays(options.staleAfterDays);
  const feedbackExists = await feedbackTableExists();
  const recentFeedbackGuard = feedbackExists
    ? `AND NOT EXISTS (
         SELECT 1
         FROM feedback f
         WHERE f.claim_id = c.id
           AND f.ts >= CURRENT_TIMESTAMP - INTERVAL '${staleAfterDays} days'
       )`
    : '';

  const claimIds = await withDedicatedConnection(async (conn) => {
    const reader = await conn.runAndReadAll(
      `
        SELECT c.id
        FROM claims c
        WHERE c.memory_type = 'working_state'
          AND COALESCE(c.status, 'active') = 'active'
          AND COALESCE(c.recency_anchor, c.created_at) < CURRENT_TIMESTAMP - INTERVAL '${staleAfterDays} days'
          ${recentFeedbackGuard}
      `
    );
    const rows = reader.getRowObjects() as Array<{ id: string }>;
    return rows.map((row) => row.id);
  });

  if (claimIds.length === 0) {
    return [];
  }

  const placeholders = claimIds.map((_, index) => `$${index + 1}`).join(',');
  await withWriteConnection(async (writeConn) => {
    await writeConn.run(
      `UPDATE claims
       SET status = 'stale',
           updated_at = CURRENT_TIMESTAMP
       WHERE id IN (${placeholders})`,
      claimIds
    );
  });

  return claimIds;
}

export interface RollbackClaimInput {
  tombstone_at: string;
  rollback_reason: string;
  superseded_by: string;
}

export async function markClaimRolledBack(id: string, input: RollbackClaimInput): Promise<void> {
  await withWriteConnection(async (conn) => {
    await conn.run(
      `UPDATE claims
       SET tombstone = TRUE,
           tombstone_at = $1::TIMESTAMP,
           rollback_reason = $2,
           superseded_by = $3,
           updated_at = CURRENT_TIMESTAMP
       WHERE id = $4`,
      [input.tombstone_at, input.rollback_reason, input.superseded_by, id]
    );
  });
}

export async function findClaimsByIds(ids: string[]): Promise<Claim[]> {
  if (ids.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const placeholders = ids.map((_, i) => `$${i + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT ${CLAIM_COLUMNS}
     FROM claims c
     WHERE c.id IN (${placeholders})
       AND ${activeClaimFilter('c')}`,
    ids
  );
  const rawRows = reader.getRowObjects() as unknown as ClaimRow[];
  const claims = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  const claimsById = new Map(claims.map((claim) => [claim.id, claim]));
  return ids.map((id) => claimsById.get(id)).filter((claim): claim is Claim => claim !== undefined);
}

/**
 * DBに登録されているClaimの総数を取得
 * サーバー再起動時の状態復元に使用
 */
export async function countClaims(): Promise<number> {
  return withDedicatedConnection(async (conn) => {
    const reader = await conn.runAndReadAll(
      `SELECT COUNT(*) as cnt
       FROM claims c
       WHERE ${activeClaimFilter('c')}`
    );
    const rows = reader.getRowObjects() as unknown as { cnt: number | bigint }[];
    return rows[0] ? Number(rows[0].cnt) : 0;
  });
}

/**
 * Claimを登録し、埋め込みベクトルも生成・保存（ADR-0004対応）
 *
 * TLA+ 対応:
 * - 新規Claimの場合のみ埋め込みを生成
 * - 埋め込み生成失敗時もClaim登録は成功（ベストエフォート）
 *
 * @param c Claim（idなし）
 * @param embeddingService 埋め込みサービス
 * @returns UpsertResult（isNew: 新規かどうか）
 */
export async function upsertClaimWithEmbedding(
  c: ClaimInput,
  embeddingService: EmbeddingService,
  connection?: DuckDBConnection
): Promise<UpsertResult> {
  // 1. 既存upsertClaim呼び出し
  const result = await upsertClaim(c, connection);

  // 2. 新規の場合のみ埋め込み生成・保存
  if (result.isNew) {
    const sensitivity: SensitivityLevel =
      c.boundary_class === 'public'
        ? 'public'
        : c.boundary_class === 'internal'
          ? 'internal'
          : 'confidential'; // pii/secret は redact-before-embed

    const embedResult = await embeddingService.embed({
      text: c.text,
      sensitivity,
    })();

    // 埋め込み生成成功時のみ保存（失敗時はClaim登録だけ成功）
    if (E.isRight(embedResult)) {
      try {
        await saveClaimVector(
          result.claim.id,
          embedResult.right.embedding,
          embedResult.right.modelVersion,
          connection
        );
      } catch {
        // ベクトル保存失敗は無視（ベストエフォート）
        // Claim登録は成功しているので、検索時はText-onlyで動作
      }
    }
  }

  return result;
}

/**
 * Vector search + embedding CRUD
 * @see docs/adr/0004-hybrid-search-design.md
 */

import { getConnection } from '../../db/connection.js';
import type { Claim } from '../claims.js';
import * as E from 'fp-ts/Either';
import { validateEmbedding } from '../../domain/validation.js';
import { normalizeRowsTimestamps } from '../../utils/serialization.js';
import {
  type SearchResult,
  type ClaimSearchFilters,
  type SimilarClaimMatch,
  type NewerSimilarClaimMatch,
  type SimilarClaimRow,
  type NewerSimilarClaimRow,
  K_VEC,
  activeClaimFilter,
  normalizeLimit,
  buildClaimFilterConditions,
  buildTextPreview,
  normalizeSimilarity,
} from './types.js';

/**
 * ベクトル検索（cos_sim）
 * TLA+ C_VecSearch: スコープ内のベクトル類似候補を取得
 *
 * @param queryEmbedding クエリの埋め込みベクトル
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @returns スコア付き検索結果
 */
export async function vectorSearch(
  queryEmbedding: readonly number[],
  scopes: string[],
  limit: number = K_VEC,
  filters: ClaimSearchFilters = {}
): Promise<SearchResult[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  // 埋め込みベクトルの検証
  const embeddingResult = validateEmbedding(queryEmbedding);
  if (E.isLeft(embeddingResult)) {
    throw new Error(embeddingResult.left.message);
  }

  const conn = await getConnection();
  const normalizedLimit = normalizeLimit(limit);

  // claim_vectorsが空の場合は空配列を返す
  const countReader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM claim_vectors');
  const countRows = countReader.getRowObjects() as unknown as { cnt: number | bigint }[];
  if (!countRows[0] || Number(countRows[0].cnt) === 0) {
    return [];
  }

  // スコープのプレースホルダー構築
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(',');
  const filterConditions = buildClaimFilterConditions('c', filters, scopes.length + 1);

  // DuckDB Node APIは配列パラメータを直接サポートしないため、
  // 配列リテラル文字列として埋め込む（検証済みなので安全）
  const embeddingLiteral = `[${[...queryEmbedding].join(',')}]`;

  // cos_simマクロでベクトル類似度計算
  // TLA+ claimVecRelevant: cos_sim >= threshold で判定
  // norm_cosで[-1,1]を[0,1]に正規化
  const sql = `
    SELECT
      c.id, c.text, c.kind, c.scope, c.boundary_class, c.memory_type, c.status, c.content_hash,
      c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
      c.retrieval_count, c.last_retrieved_at,
      norm_cos(cos_sim(cv.embedding, ${embeddingLiteral}::DOUBLE[])) as vec_score
    FROM claims c
    INNER JOIN claim_vectors cv ON cv.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
      AND ${activeClaimFilter('c')}
      ${filterConditions.sql ? `AND ${filterConditions.sql}` : ''}
    ORDER BY vec_score DESC, c.created_at DESC
    LIMIT $${scopes.length + filterConditions.params.length + 1}
  `;

  const reader = await conn.runAndReadAll(sql, [
    ...scopes,
    ...filterConditions.params,
    normalizedLimit,
  ]);
  const rawRows = reader.getRowObjects() as unknown as (Claim & { vec_score: number })[];
  const rows = normalizeRowsTimestamps(rawRows);

  return rows.map((row) => ({
    claim: {
      id: row.id,
      text: row.text,
      kind: row.kind,
      scope: row.scope,
      boundary_class: row.boundary_class,
      memory_type: row.memory_type ?? null,
      status: row.status ?? 'active',
      content_hash: row.content_hash,
      utility: row.utility,
      confidence: row.confidence,
      created_at: row.created_at,
      updated_at: row.updated_at,
      recency_anchor: row.recency_anchor,
      retrieval_count: Number(row.retrieval_count ?? 0),
      last_retrieved_at: row.last_retrieved_at ?? null,
    },
    score: row.vec_score,
  }));
}

// ========== claim_vectors操作 ==========

/**
 * Claimの埋め込みベクトルを保存
 *
 * @param claimId Claim ID
 * @param embedding 埋め込みベクトル
 * @param modelVersion モデルバージョン
 */
export async function saveClaimVector(
  claimId: string,
  embedding: readonly number[],
  modelVersion: string
): Promise<void> {
  // 埋め込みベクトルの検証（SQLインジェクション防止）
  const saveEmbeddingResult = validateEmbedding(embedding);
  if (E.isLeft(saveEmbeddingResult)) {
    throw new Error(saveEmbeddingResult.left.message);
  }

  const conn = await getConnection();
  // DuckDB Node APIは配列パラメータを直接サポートしないため、
  // 配列リテラル文字列として埋め込む（検証済みなので安全）
  const embeddingLiteral = `[${embedding.join(',')}]`;
  await conn.run(
    `INSERT INTO claim_vectors (claim_id, embedding, model_version)
     VALUES ($1, ${embeddingLiteral}::DOUBLE[], $2)
     ON CONFLICT (claim_id)
     DO UPDATE SET embedding = EXCLUDED.embedding, model_version = EXCLUDED.model_version`,
    [claimId, modelVersion]
  );
}

/**
 * Claimの埋め込みベクトルを取得
 *
 * @param claimId Claim ID
 * @returns 埋め込みベクトル（存在しない場合undefined）
 */
export async function getClaimVector(claimId: string): Promise<readonly number[] | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT embedding FROM claim_vectors WHERE claim_id = $1',
    [claimId]
  );
  const rows = reader.getRowObjects();

  if (rows.length === 0) {
    return undefined;
  }

  const row = rows[0] as Record<string, unknown>;
  const embedding = row['embedding'];

  if (embedding == null) {
    return undefined;
  }

  // すでにnumber[]の場合
  if (Array.isArray(embedding)) {
    return embedding as number[];
  }

  // DuckDB Node APIはDOUBLE[]配列をDuckDBListValueオブジェクトとして返す
  // DuckDBListValue: { items: number[] } 形式
  if (typeof embedding === 'object' && 'items' in embedding) {
    const listValue = embedding as { items: number[] };
    if (Array.isArray(listValue.items)) {
      return listValue.items;
    }
  }

  // Float64Arrayの場合
  if (embedding instanceof Float64Array || ArrayBuffer.isView(embedding)) {
    return Array.from(embedding as Float64Array);
  }

  return undefined;
}

export async function findSimilarActiveClaims(
  claimId: string,
  threshold: number = 0.85
): Promise<SimilarClaimMatch[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT
       candidate.id,
       cos_sim(base_cv.embedding, candidate_cv.embedding) AS similarity,
       candidate.text,
       candidate.created_at
     FROM claims base
     INNER JOIN claim_vectors base_cv ON base_cv.claim_id = base.id
     INNER JOIN claims candidate
       ON candidate.scope = base.scope
      AND candidate.id <> base.id
      AND candidate.content_hash <> base.content_hash
      AND ${activeClaimFilter('candidate')}
     INNER JOIN claim_vectors candidate_cv ON candidate_cv.claim_id = candidate.id
     WHERE base.id = $1
       AND ${activeClaimFilter('base')}
       AND cos_sim(base_cv.embedding, candidate_cv.embedding) > $2
     ORDER BY similarity DESC, candidate.created_at DESC, candidate.id DESC`,
    [claimId, threshold]
  );
  const rawRows = reader.getRowObjects() as unknown as SimilarClaimRow[];
  const rows = normalizeRowsTimestamps(rawRows) as SimilarClaimRow[];

  return rows.map((row) => ({
    id: row.id,
    similarity: normalizeSimilarity(row.similarity),
    text_preview: buildTextPreview(row.text),
    created_at:
      typeof row.created_at === 'string' ? row.created_at : new Date(row.created_at).toISOString(),
  }));
}

export async function findNewerSimilarClaims(
  claimIds: readonly string[],
  threshold: number = 0.85
): Promise<Map<string, NewerSimilarClaimMatch>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, index) => `$${index + 1}`).join(',');
  const thresholdParam = `$${claimIds.length + 1}`;
  const reader = await conn.runAndReadAll(
    `SELECT claim_id, newer_similar, similarity, newer_created_at
     FROM (
       SELECT
         candidates.*,
         ROW_NUMBER() OVER (
           PARTITION BY claim_id
           ORDER BY newer_created_at DESC, newer_vector_rowid DESC, similarity DESC, newer_similar DESC
         ) AS rn
       FROM (
         SELECT
           base.id AS claim_id,
           newer.id AS newer_similar,
           cos_sim(base_cv.embedding, newer_cv.embedding) AS similarity,
            newer.created_at AS newer_created_at,
           newer_cv.rowid AS newer_vector_rowid
         FROM claims base
         INNER JOIN claim_vectors base_cv ON base_cv.claim_id = base.id
         INNER JOIN claims newer
           ON newer.scope = base.scope
          AND newer.id <> base.id
          AND newer.content_hash <> base.content_hash
          AND ${activeClaimFilter('newer')}
         INNER JOIN claim_vectors newer_cv ON newer_cv.claim_id = newer.id
         WHERE base.id IN (${placeholders})
           AND ${activeClaimFilter('base')}
           AND (
             newer.created_at > base.created_at
             OR (
               newer.created_at = base.created_at
               AND newer_cv.rowid > base_cv.rowid
             )
           )
           AND cos_sim(base_cv.embedding, newer_cv.embedding) > ${thresholdParam}
       ) AS candidates
     ) AS ranked
     WHERE rn = 1`,
    [...claimIds, threshold]
  );
  const rawRows = reader.getRowObjects() as unknown as NewerSimilarClaimRow[];
  const rows = normalizeRowsTimestamps(rawRows) as NewerSimilarClaimRow[];

  return new Map(
    rows.map((row) => [
      row.claim_id,
      {
        freshness: 'stale_candidate' as const,
        newer_similar: row.newer_similar,
        similarity: normalizeSimilarity(row.similarity),
        created_at:
          typeof row.newer_created_at === 'string'
            ? row.newer_created_at
            : new Date(row.newer_created_at).toISOString(),
      },
    ])
  );
}

/**
 * Claimの埋め込みベクトルを削除
 *
 * @param claimId Claim ID
 */
export async function deleteClaimVector(claimId: string): Promise<void> {
  const conn = await getConnection();
  await conn.run('DELETE FROM claim_vectors WHERE claim_id = $1', [claimId]);
}

/**
 * Text search SQL + scoring
 * @see docs/adr/0004-hybrid-search-design.md
 */

import { getConnection } from '../../db/connection.js';
import type { Claim } from '../claims.js';
import { normalizeRowsTimestamps } from '../../utils/serialization.js';
import {
  type SearchResult,
  type ClaimSearchFilters,
  K_TEXT,
  DEFAULT_CRITIC_SCORE,
  activeClaimFilter,
  splitQueryWords,
  buildWordOrCondition,
  buildClaimFilterConditions,
  normalizeLimit,
} from './types.js';

/**
 * テキスト検索（ILIKE + 単語分割OR検索）
 * TLA+ C_TextSearch: スコープ内のテキスト一致候補を取得
 *
 * 検索クエリは空白（半角・全角）で分割され、各単語のいずれかを含むClaimがマッチ。
 * 例: "状態管理 XState Valtio" → "状態管理" OR "XState" OR "Valtio"
 *
 * @param query 検索クエリ文字列（空白区切りで複数単語指定可能）
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @returns スコア付き検索結果
 */
export async function textSearch(
  query: string,
  scopes: string[],
  limit: number = K_TEXT,
  filters: ClaimSearchFilters = {}
): Promise<SearchResult[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const normalizedLimit = normalizeLimit(limit);

  // スコープのプレースホルダー構築
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(',');

  // クエリを単語に分割
  const words = splitQueryWords(query);

  // 空クエリの場合はスコープ内の全Claimを返す（criticスコア順）
  if (words.length === 0) {
    const filterConditions = buildClaimFilterConditions('c', filters, scopes.length + 1);
    const sql = `
      SELECT
        c.id, c.text, c.kind, c.scope, c.boundary_class, c.memory_type, c.status, c.content_hash,
        c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
        c.retrieval_count, c.last_retrieved_at,
        COALESCE(cr.score, ${DEFAULT_CRITIC_SCORE}) as text_score
      FROM claims c
      LEFT JOIN critic cr ON cr.claim_id = c.id
      WHERE c.scope IN (${scopePlaceholders})
        AND ${activeClaimFilter('c')}
        ${filterConditions.sql ? `AND ${filterConditions.sql}` : ''}
      ORDER BY text_score DESC, c.created_at DESC
      LIMIT $${scopes.length + filterConditions.params.length + 1}
    `;
    const reader = await conn.runAndReadAll(sql, [
      ...scopes,
      ...filterConditions.params,
      normalizedLimit,
    ]);
    const rawRows = reader.getRowObjects() as unknown as (Claim & { text_score: number })[];
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
      score: row.text_score,
    }));
  }

  // 単語OR条件を構築
  const { sql: wordCondition, params: wordParams } = buildWordOrCondition(words, scopes.length + 1);
  const filterConditions = buildClaimFilterConditions(
    'c',
    filters,
    scopes.length + wordParams.length + 1
  );

  // criticスコアとテキストマッチを組み合わせたスコア計算
  // TLA+ claimTextRelevant: いずれかの単語に対して LIKE '%word%' でマッチ
  const sql = `
    SELECT
      c.id, c.text, c.kind, c.scope, c.boundary_class, c.memory_type, c.status, c.content_hash,
      c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
      c.retrieval_count, c.last_retrieved_at,
      COALESCE(cr.score, ${DEFAULT_CRITIC_SCORE}) as text_score
    FROM claims c
    LEFT JOIN critic cr ON cr.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
      AND ${activeClaimFilter('c')}
      AND ${wordCondition}
      ${filterConditions.sql ? `AND ${filterConditions.sql}` : ''}
    ORDER BY text_score DESC, c.created_at DESC
    LIMIT $${scopes.length + wordParams.length + filterConditions.params.length + 1}
  `;

  const reader = await conn.runAndReadAll(sql, [
    ...scopes,
    ...wordParams,
    ...filterConditions.params,
    normalizedLimit,
  ]);
  const rawRows = reader.getRowObjects() as unknown as (Claim & { text_score: number })[];
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
    score: row.text_score,
  }));
}

/**
 * クエリなしの場合のフォールバック
 * criticスコアでソートして返す（既存listClaimsByScopeと同等）
 */
export async function fallbackToTextOnlyResults(
  scopes: string[],
  limit?: number,
  filters: ClaimSearchFilters = {}
): Promise<SearchResult[]> {
  // 空scopesの早期リターン（hybridSearchで既にチェック済みだが防御的に）
  if (scopes.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(',');
  const filterConditions = buildClaimFilterConditions('c', filters, scopes.length + 1);

  const limitClause =
    limit !== undefined ? `LIMIT $${scopes.length + filterConditions.params.length + 1}` : '';
  const sql = `
    SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.memory_type, c.status, c.content_hash,
           c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
           c.retrieval_count, c.last_retrieved_at,
           COALESCE(cr.score, 0) as score
    FROM claims c
    LEFT JOIN critic cr ON cr.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
      AND ${activeClaimFilter('c')}
      ${filterConditions.sql ? `AND ${filterConditions.sql}` : ''}
    ORDER BY score DESC, c.created_at DESC
    ${limitClause}
  `;

  const params =
    limit !== undefined
      ? [...scopes, ...filterConditions.params, limit]
      : [...scopes, ...filterConditions.params];
  const reader = await conn.runAndReadAll(sql, params);
  const rawRows = reader.getRowObjects() as unknown as (Claim & { score: number })[];
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
    score: row.score,
  }));
}

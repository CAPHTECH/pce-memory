/**
 * Observation Store（Issue #30）
 * - Observation（生データ）を短期TTLで保持
 * - 期限後は content を scrub（NULL化）して最小証跡（digest等）のみ残す
 */
import { getConnection } from '../db/connection.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';
import type { Claim } from './claims.js';
import { escapeLikePattern, splitQueryWords } from './hybridSearch.js';
import { recencyDecay } from './rerank.js';

export type ObservationSourceType = 'chat' | 'tool' | 'file' | 'http' | 'system';

export interface Observation {
  id: string;
  source_type: ObservationSourceType;
  source_id?: string;
  content?: string | null;
  boundary_class: string;
  content_digest: string;
  content_length: number;
  actor?: string;
  tags?: unknown;
  created_at?: Date | string;
  expires_at?: Date | string;
}

export interface ActivatedObservationClaim extends Claim {
  observation_id: string;
  content: string;
  source_type: ObservationSourceType;
  actor?: string | null;
  tags?: string[] | null;
  expires_at?: Date | string | null;
  transient: true;
  source_record_type: 'observation';
}

export interface ObservationSearchFilters {
  boundaryClasses?: string[];
  limit?: number;
}

export interface ScoredObservation {
  claim: ActivatedObservationClaim;
  score: number;
  source_layer: 'micro';
}

export const OBSERVATION_RECENCY_HALF_LIFE_DAYS = 1;
export const OBSERVATION_MAX_SCORE = 0.8;

export interface InsertObservationInput {
  id: string;
  source_type: ObservationSourceType;
  source_id?: string;
  content: string | null;
  boundary_class: string;
  content_digest: string;
  content_length: number;
  actor?: string;
  tags?: string[];
  expires_at: string;
}

export async function insertObservation(input: InsertObservationInput): Promise<Observation> {
  const conn = await getConnection();
  const tagsJson = input.tags ? JSON.stringify(input.tags) : null;

  await conn.run(
    'INSERT INTO observations (id, source_type, source_id, content, boundary_class, content_digest, content_length, actor, tags, expires_at) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10::TIMESTAMP)',
    [
      input.id,
      input.source_type,
      input.source_id ?? null,
      input.content,
      input.boundary_class,
      input.content_digest,
      input.content_length,
      input.actor ?? null,
      tagsJson,
      input.expires_at,
    ]
  );

  const reader = await conn.runAndReadAll(
    'SELECT id, source_type, source_id, content, boundary_class, content_digest, content_length, actor, tags, created_at, expires_at FROM observations WHERE id = $1',
    [input.id]
  );
  const rawRows = reader.getRowObjects() as unknown as Observation[];
  const rows = normalizeRowsTimestamps(rawRows);
  return rows[0]!;
}

export async function findObservationById(id: string): Promise<Observation | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, source_type, source_id, content, boundary_class, content_digest, content_length, actor, tags, created_at, expires_at FROM observations WHERE id = $1',
    [id]
  );
  const rawRows = reader.getRowObjects() as unknown as Observation[];
  const rows = normalizeRowsTimestamps(rawRows);
  return rows[0];
}

export async function findObservationsByIds(ids: string[]): Promise<Observation[]> {
  if (ids.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const placeholders = ids.map((_, i) => `$${i + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT id, source_type, source_id, content, boundary_class, content_digest, content_length, actor, tags, created_at, expires_at
     FROM observations
     WHERE id IN (${placeholders})`,
    ids
  );
  const rawRows = reader.getRowObjects() as unknown as Observation[];
  return normalizeRowsTimestamps(rawRows);
}

function buildObservationBoundaryFilterCondition(
  boundaryClasses: readonly string[] | undefined,
  startParamIndex: number
): { sql: string; params: string[] } {
  if (boundaryClasses === undefined) {
    return { sql: '', params: [] };
  }

  const normalizedBoundaryClasses = [...new Set(boundaryClasses.filter((bc) => bc.length > 0))];
  if (normalizedBoundaryClasses.length === 0) {
    return { sql: '1 = 0', params: [] };
  }

  const placeholders = normalizedBoundaryClasses
    .map((_, index) => `$${startParamIndex + index}`)
    .join(',');

  return {
    sql: `o.boundary_class IN (${placeholders})`,
    params: normalizedBoundaryClasses,
  };
}

function parseObservationTags(tags: unknown): string[] | null {
  if (Array.isArray(tags) && tags.every((tag) => typeof tag === 'string')) {
    return tags;
  }

  if (typeof tags === 'string') {
    try {
      const parsed = JSON.parse(tags) as unknown;
      return Array.isArray(parsed) && parsed.every((tag) => typeof tag === 'string')
        ? parsed
        : null;
    } catch {
      return null;
    }
  }

  return null;
}

function buildActivatedObservationClaim(
  observation: Observation
): ActivatedObservationClaim | null {
  if (typeof observation.content !== 'string' || observation.content.length === 0) {
    return null;
  }

  const createdAt = observation.created_at ?? new Date(0).toISOString();

  return {
    id: observation.id,
    observation_id: observation.id,
    text: observation.content,
    content: observation.content,
    kind: 'observation',
    scope: 'session',
    boundary_class: observation.boundary_class,
    memory_type: null,
    status: 'active',
    content_hash: observation.content_digest,
    utility: 0,
    confidence: 1,
    created_at: createdAt,
    updated_at: createdAt,
    recency_anchor: createdAt,
    retrieval_count: 0,
    last_retrieved_at: null,
    source_type: observation.source_type,
    actor: observation.actor ?? null,
    tags: parseObservationTags(observation.tags),
    expires_at: observation.expires_at ?? null,
    transient: true,
    source_record_type: 'observation',
  };
}

function calculateObservationScore(textScore: number, createdAt: Date | string): number {
  const normalizedTextScore = Math.max(0, Math.min(1, textScore));
  const recencyScore = recencyDecay(createdAt, OBSERVATION_RECENCY_HALF_LIFE_DAYS);
  return normalizedTextScore * Math.min(recencyScore, OBSERVATION_MAX_SCORE);
}

export async function searchObservationsWithScores(
  query?: string,
  filters: ObservationSearchFilters = {}
): Promise<ScoredObservation[]> {
  const conn = await getConnection();
  const words = splitQueryWords(query ?? '');
  const boundary = buildObservationBoundaryFilterCondition(filters.boundaryClasses, 1);
  const whereClauses = [
    'o.content IS NOT NULL',
    '(o.expires_at IS NULL OR o.expires_at > CURRENT_TIMESTAMP)',
  ];

  if (boundary.sql) {
    whereClauses.push(boundary.sql);
  }

  const params: Array<string | number> = [...boundary.params];
  let textScoreExpr = '1.0';

  if (words.length > 0) {
    const wordStartIndex = params.length + 1;
    const patterns = words.map((word) => `%${escapeLikePattern(word)}%`);
    params.push(...patterns);

    const matchExpressions = patterns.map(
      (_, index) =>
        `CASE WHEN o.content ILIKE $${wordStartIndex + index} ESCAPE '\\' THEN 1 ELSE 0 END`
    );
    const matchCondition = matchExpressions
      .map((_, index) => `o.content ILIKE $${wordStartIndex + index} ESCAPE '\\'`)
      .join(' OR ');

    textScoreExpr = `(${matchExpressions.join(' + ')})::DOUBLE / ${words.length}`;
    whereClauses.push(`(${matchCondition})`);
  }

  const recencyExpr = `exp((-0.693147 * GREATEST(
      0.0,
      (epoch(CURRENT_TIMESTAMP) - epoch(COALESCE(o.created_at, CURRENT_TIMESTAMP))) / 86400.0
    )) / ${OBSERVATION_RECENCY_HALF_LIFE_DAYS})`;
  const finalScoreExpr = `(${textScoreExpr}) * LEAST(${recencyExpr}, ${OBSERVATION_MAX_SCORE})`;
  const limit =
    typeof filters.limit === 'number' && Number.isFinite(filters.limit) && filters.limit > 0
      ? Math.floor(filters.limit)
      : undefined;
  const limitClause = limit !== undefined ? `LIMIT $${params.length + 1}` : '';
  if (limit !== undefined) {
    params.push(limit);
  }

  const sql = `
    SELECT
      o.id,
      o.source_type,
      o.source_id,
      o.content,
      o.boundary_class,
      o.content_digest,
      o.content_length,
      o.actor,
      o.tags,
      o.created_at,
      o.expires_at,
      ${textScoreExpr} AS text_score,
      ${finalScoreExpr} AS final_score
    FROM observations o
    WHERE ${whereClauses.join(' AND ')}
    ORDER BY final_score DESC, o.created_at DESC
    ${limitClause}
  `;

  const reader = await conn.runAndReadAll(sql, params);
  const rawRows = reader.getRowObjects() as unknown as Array<
    Observation & { text_score: number; final_score: number }
  >;
  const rows = normalizeRowsTimestamps(rawRows);

  return rows
    .map((row) => {
      const claim = buildActivatedObservationClaim(row);
      if (!claim) {
        return null;
      }

      const textScore = typeof row.text_score === 'number' ? row.text_score : 0;
      const score =
        typeof row.final_score === 'number'
          ? row.final_score
          : calculateObservationScore(textScore, claim.created_at);

      return {
        claim,
        score,
        source_layer: 'micro' as const,
      };
    })
    .filter((row): row is ScoredObservation => row !== null);
}

export type ObservationGcMode = 'scrub' | 'delete';

/**
 * 期限切れObservationのGC
 * - scrub: content, actor, source_id, tagsをNULL化（推奨）
 *   → PIIがmetadataに含まれる可能性があるため、contentだけでなく関連フィールドも消去
 * - delete: row削除（監査目的での保持が不要な場合）
 */
export async function gcExpiredObservations(mode: ObservationGcMode = 'scrub'): Promise<void> {
  const conn = await getConnection();
  if (mode === 'delete') {
    await conn.run(
      'DELETE FROM observations WHERE expires_at IS NOT NULL AND expires_at <= CURRENT_TIMESTAMP'
    );
    return;
  }
  // Issue #30 Review: actor, source_id, tags にもPII（メールアドレス、URL含むユーザーID等）が
  // 含まれる可能性があるため、TTL後はすべてNULL化してデータ最小化を徹底
  await conn.run(
    `UPDATE observations
     SET content = NULL, actor = NULL, source_id = NULL, tags = NULL
     WHERE expires_at IS NOT NULL
       AND expires_at <= CURRENT_TIMESTAMP
       AND (content IS NOT NULL OR actor IS NOT NULL OR source_id IS NOT NULL OR tags IS NOT NULL)`
  );
}

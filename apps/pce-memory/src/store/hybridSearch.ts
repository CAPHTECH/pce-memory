/**
 * Hybrid Search実装（ADR-0004 設計C準拠）
 *
 * TLA+ 不変条件対応:
 * - Inv_C_ScopeConsistency: WHERE scope IN (...) でスコープフィルタ
 * - Inv_C_ThresholdFiltering: WHERE score >= THRESHOLD でフィルタ
 * - Inv_C_MergeComplete: Promise.all + union merge で両検索結果統合
 * - Inv_C_FusionCorrectness: hybrid_score(text, vec, α) で融合
 *
 * パラメータ（ADR-0004より）:
 * - α (ALPHA) = 0.65: ベクトル重視
 * - THRESHOLD = 0.15: 低ノイズフィルタ
 * - k_text = 48: テキスト検索上限
 * - k_vec = 96: ベクトル検索上限
 *
 * @see docs/adr/0004-hybrid-search-design.md
 * @see docs/spec/tlaplus/hybrid_search_simple.tla
 */

import { getConnection } from '../db/connection.js';
import type { Claim } from './claims.js';
import type { EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import {
  adjustRecencyTerm,
  calculateGFromClaim,
  calculateIntentScoreBreakdown,
  calculateProvenanceQualityBreakdown,
  calculateScoreBreakdown,
  type GFactorBreakdown,
  type ScoreBreakdown,
} from './rerank.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';
import type { ActivateIntent, ClaimKind, ClaimStatus, MemoryType } from '../domain/types.js';

// ========== ADR-0004 パラメータ ==========

/** ベクトル検索重み（TLA+ Alpha = 65 / 100） */
const ALPHA = 0.65;

/** 採用閾値（TLA+ Threshold = 15 / 100） */
const THRESHOLD = 0.15;

/** テキスト検索上限（3× of k_final） */
const K_TEXT = 48;

/** ベクトル検索上限（6× of k_final） */
const K_VEC = 96;

/** MMR関連デフォルト値 */
const DEFAULT_MMR_LAMBDA = 0.72;
const DEFAULT_MMR_MAX_CANDIDATES = 48;

/** Query expansion関連デフォルト値 */
const DEFAULT_QUERY_EXPANSION_MAX_SEED_ENTITIES = 3;
const DEFAULT_QUERY_EXPANSION_MAX_RELATED_ENTITIES = 8;
const DEFAULT_QUERY_EXPANSION_MAX_TERMS = 6;

/** criticスコアが存在しない場合のデフォルト値 */
const DEFAULT_CRITIC_SCORE = 0.5;

/** 最小limit値 */
const MIN_LIMIT = 1;

/** 埋め込み次元数の上限（一般的なモデルの最大値） */
const MAX_EMBEDDING_DIM = 4096;

/** 埋め込み値の絶対値上限（正規化ベクトルは通常[-1, 1]範囲） */
const MAX_EMBEDDING_MAGNITUDE = 10.0;

// ========== ユーティリティ関数 ==========

function activeClaimFilter(alias: string): string {
  return `COALESCE(${alias}.tombstone, FALSE) = FALSE
    AND NOT EXISTS (
      SELECT 1
      FROM promotion_queue pq
      WHERE pq.accepted_claim_id = ${alias}.id
        AND pq.status = 'rolled_back'
    )`;
}

/**
 * 埋め込みベクトルが有効か検証
 * - 空ベクトル禁止
 * - 次元数上限チェック（DoS防止）
 * - 各値の有限性チェック（NaN/Infinity禁止）
 * - 各値の絶対値上限チェック（異常値検出）
 *
 * @param embedding 検証対象のベクトル
 * @throws Error 不正な値が含まれる場合
 */
function validateEmbedding(embedding: readonly number[]): void {
  if (embedding.length === 0) {
    throw new Error('Embedding vector must not be empty');
  }
  if (embedding.length > MAX_EMBEDDING_DIM) {
    throw new Error(`Embedding dimension ${embedding.length} exceeds maximum ${MAX_EMBEDDING_DIM}`);
  }
  for (let i = 0; i < embedding.length; i++) {
    const v = embedding[i];
    if (typeof v !== 'number' || !Number.isFinite(v)) {
      throw new Error(`Invalid embedding value at index ${i}: ${v}`);
    }
    if (Math.abs(v) > MAX_EMBEDDING_MAGNITUDE) {
      throw new Error(
        `Embedding value ${v} at index ${i} exceeds magnitude limit ${MAX_EMBEDDING_MAGNITUDE}`
      );
    }
  }
}

/**
 * LIKEパターンの特殊文字をエスケープ
 * @param query 検索クエリ
 * @returns エスケープ済みクエリ
 */
export function escapeLikePattern(query: string): string {
  // DuckDBのLIKE: % と _ が特殊文字
  return query.replace(/[%_\\]/g, '\\$&');
}

/**
 * クエリを単語に分割（全角・半角空白対応）
 * 空白文字（半角スペース、タブ、改行、全角スペース）で分割し、空文字を除去
 *
 * @param query 検索クエリ
 * @returns 単語配列（空文字を除去済み）
 */
export function splitQueryWords(query: string): string[] {
  // \s: 半角スペース、タブ、改行など
  // \u3000: 全角スペース
  return query.split(/[\s\u3000]+/).filter((word) => word.length > 0);
}

/**
 * 複数単語用のILIKE OR条件を構築
 * 各単語をエスケープし、OR条件で結合したSQL条件を生成
 *
 * @param words 単語配列
 * @param startParamIndex プレースホルダー開始インデックス
 * @returns { sql: string, params: string[] } - SQL条件とパラメータ配列
 */
export function buildWordOrCondition(
  words: string[],
  startParamIndex: number
): { sql: string; params: string[] } {
  if (words.length === 0) {
    return { sql: '', params: [] };
  }

  if (words.length === 1) {
    // 単一単語: 従来と同じ形式
    const escaped = escapeLikePattern(words[0]!);
    return {
      sql: `c.text ILIKE $${startParamIndex} ESCAPE '\\'`,
      params: [`%${escaped}%`],
    };
  }

  // 複数単語: OR条件
  const conditions: string[] = [];
  const params: string[] = [];

  for (let i = 0; i < words.length; i++) {
    const escaped = escapeLikePattern(words[i]!);
    conditions.push(`c.text ILIKE $${startParamIndex + i} ESCAPE '\\'`);
    params.push(`%${escaped}%`);
  }

  return {
    sql: `(${conditions.join(' OR ')})`,
    params,
  };
}

/**
 * limit値を正規化（最小値保証）
 * @param limit 元のlimit値
 * @returns 正規化されたlimit値
 */
function normalizeLimit(limit: number): number {
  return Math.max(MIN_LIMIT, Math.floor(limit));
}

/**
 * boundary_classフィルタを構築
 * 未指定時はフィルタなし、空配列時は常に0件にする
 */
function buildBoundaryFilterCondition(
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
    sql: `c.boundary_class IN (${placeholders})`,
    params: normalizedBoundaryClasses,
  };
}

function buildColumnFilterCondition(
  alias: string,
  column: string,
  values: readonly string[] | undefined,
  startParamIndex: number
): { sql: string; params: string[] } {
  if (values === undefined) {
    return { sql: '', params: [] };
  }

  const normalizedValues = [...new Set(values.filter((value) => value.length > 0))];
  if (normalizedValues.length === 0) {
    return { sql: '1 = 0', params: [] };
  }

  const placeholders = normalizedValues.map((_, index) => `$${startParamIndex + index}`).join(',');

  return {
    sql: `${alias}.${column} IN (${placeholders})`,
    params: normalizedValues,
  };
}

function buildClaimFilterConditions(
  alias: string,
  filters: ClaimSearchFilters,
  startParamIndex: number
): { sql: string; params: string[] } {
  let nextParamIndex = startParamIndex;
  const clauses: string[] = [];
  const params: string[] = [];

  const boundary = buildBoundaryFilterCondition(filters.boundaryClasses, nextParamIndex);
  if (boundary.sql) {
    clauses.push(boundary.sql);
    params.push(...boundary.params);
    nextParamIndex += boundary.params.length;
  }

  const kind = buildColumnFilterCondition(alias, 'kind', filters.kindFilter, nextParamIndex);
  if (kind.sql) {
    clauses.push(kind.sql);
    params.push(...kind.params);
    nextParamIndex += kind.params.length;
  }

  const memoryType = buildColumnFilterCondition(
    alias,
    'memory_type',
    filters.memoryTypeFilter,
    nextParamIndex
  );
  if (memoryType.sql) {
    clauses.push(memoryType.sql);
    params.push(...memoryType.params);
    nextParamIndex += memoryType.params.length;
  }

  const excludedStatuses = filters.excludedWorkingStateStatuses;
  if (excludedStatuses !== undefined) {
    const normalizedStatuses = [...new Set(excludedStatuses.filter((value) => value.length > 0))];
    if (normalizedStatuses.length === 0) {
      clauses.push('1 = 0');
    } else {
      const placeholders = normalizedStatuses
        .map((_, index) => `$${nextParamIndex + index}`)
        .join(',');
      clauses.push(
        `(${alias}.memory_type IS NULL OR ${alias}.memory_type <> 'working_state' OR COALESCE(${alias}.status, 'active') NOT IN (${placeholders}))`
      );
      params.push(...normalizedStatuses);
    }
  }

  return {
    sql: clauses.join(' AND '),
    params,
  };
}

// ========== 型定義 ==========

/**
 * 検索結果（スコア付き）
 * TLA+: [claim: ClaimId, score: Score]
 */
interface SearchResult {
  claim: Claim;
  score: number;
}

interface ClaimSearchFilters {
  boundaryClasses?: string[];
  kindFilter?: ClaimKind[];
  memoryTypeFilter?: MemoryType[];
  excludedWorkingStateStatuses?: ClaimStatus[];
}

export interface MmrConfig {
  enabled?: boolean;
  lambda?: number;
  maxCandidates?: number;
}

export interface QueryExpansionConfig {
  enabled?: boolean;
  maxSeedEntities?: number;
  maxRelatedEntities?: number;
  maxExpansionTerms?: number;
}

/**
 * g()再ランキング用メトリクス
 */
interface ClaimMetrics {
  id: string;
  utility: number;
  confidence: number;
  /** 有効タイムスタンプ（updated_at or created_at） */
  ts_eff: Date | string;
  kind: string;
  evidence_count: number;
  has_provenance_actor_note: boolean;
  has_promotion_lineage: boolean;
}

/**
 * utility統計情報（z-score計算用）
 */
interface UtilityStats {
  mean: number;
  std: number;
}

interface ClaimMetricsRow {
  id: string;
  utility: number;
  confidence: number;
  ts_eff: Date | string;
  kind: string;
  evidence_count: number | bigint;
  has_provenance_actor_note: number | bigint | boolean;
  has_promotion_lineage: number | bigint | boolean;
}

/**
 * g()適用済み検索結果
 */
export interface RankedSearchResult {
  claim: Claim;
  fusedScore: number;
  breakdown?: ScoreBreakdown;
}

/**
 * Hybrid Search設定
 */
export interface HybridSearchConfig {
  /** EmbeddingService（クエリ埋め込み生成用） */
  embeddingService: EmbeddingService;
  /** α係数（オプション、デフォルト0.65） */
  alpha?: number;
  /** 閾値（オプション、デフォルト0.15） */
  threshold?: number;
  /** テキスト候補上限（オプション、デフォルト48） */
  kText?: number;
  /** ベクトル候補上限（オプション、デフォルト96） */
  kVec?: number;
  /** g()再ランキングを有効化（オプション、デフォルトtrue） */
  enableRerank?: boolean;
  /** デバッグ用: スコア内訳を含める（オプション、デフォルトfalse） */
  includeBreakdown?: boolean;
  /** カーソル（ページネーション用、claim_idを使用） */
  cursor?: string;
  /** 事前に許可されたboundary_classのみに絞り込む */
  boundaryClasses?: string[];
  /** kindフィルタ */
  kindFilter?: ClaimKind[];
  /** memory_typeフィルタ */
  memoryTypeFilter?: MemoryType[];
  /** activate時に除外するworking_state status */
  excludedWorkingStateStatuses?: ClaimStatus[];
  /** activate intent */
  intent?: ActivateIntent;
  /** 実験的なMMR多様化設定 */
  mmr?: MmrConfig;
  /** 実験的なエンティティグラフ拡張設定 */
  queryExpansion?: QueryExpansionConfig;
}

/**
 * スコア付きClaim（検索結果用）
 */
export interface ScoredClaim {
  claim: Claim;
  /** 融合スコア（g()適用後） */
  score: number;
  /** スコア内訳 */
  score_breakdown?: ScoreBreakdown;
  /** source layer */
  source_layer?: string;
}

function mapScopeToLayer(scope: string): 'micro' | 'meso' | 'macro' {
  if (scope === 'principle') {
    return 'macro';
  }
  if (scope === 'project') {
    return 'meso';
  }
  return 'micro';
}

function buildTextOnlyScoreBreakdown(score: number): ScoreBreakdown {
  return {
    s_text: score,
    s_vec: 0,
    S: score,
    g: {
      utility_term: 1.0,
      confidence_term: 1.0,
      recency_term: 1.0,
      g: 1.0,
    },
    score_final: score,
  };
}

function resolveAlpha(alpha: number | undefined): number {
  return typeof alpha === 'number' && Number.isFinite(alpha) ? alpha : ALPHA;
}

function resolveThreshold(threshold: number | undefined): number {
  return typeof threshold === 'number' && Number.isFinite(threshold) ? threshold : THRESHOLD;
}

function resolveCandidateLimit(limit: number | undefined, fallback: number): number {
  return typeof limit === 'number' && Number.isFinite(limit) && limit > 0
    ? normalizeLimit(limit)
    : fallback;
}

function resolveMmrConfig(mmr: MmrConfig | undefined): Required<MmrConfig> | undefined {
  if (!mmr?.enabled) {
    return undefined;
  }

  const lambda =
    typeof mmr.lambda === 'number' && Number.isFinite(mmr.lambda) && mmr.lambda > 0 && mmr.lambda < 1
      ? mmr.lambda
      : DEFAULT_MMR_LAMBDA;

  const maxCandidates =
    typeof mmr.maxCandidates === 'number' && Number.isFinite(mmr.maxCandidates) && mmr.maxCandidates > 0
      ? normalizeLimit(mmr.maxCandidates)
      : DEFAULT_MMR_MAX_CANDIDATES;

  return {
    enabled: true,
    lambda,
    maxCandidates,
  };
}

function resolveQueryExpansionConfig(
  queryExpansion: QueryExpansionConfig | undefined
): Required<QueryExpansionConfig> | undefined {
  if (!queryExpansion?.enabled) {
    return undefined;
  }

  return {
    enabled: true,
    maxSeedEntities:
      typeof queryExpansion.maxSeedEntities === 'number' &&
      Number.isFinite(queryExpansion.maxSeedEntities) &&
      queryExpansion.maxSeedEntities > 0
        ? normalizeLimit(queryExpansion.maxSeedEntities)
        : DEFAULT_QUERY_EXPANSION_MAX_SEED_ENTITIES,
    maxRelatedEntities:
      typeof queryExpansion.maxRelatedEntities === 'number' &&
      Number.isFinite(queryExpansion.maxRelatedEntities) &&
      queryExpansion.maxRelatedEntities > 0
        ? normalizeLimit(queryExpansion.maxRelatedEntities)
        : DEFAULT_QUERY_EXPANSION_MAX_RELATED_ENTITIES,
    maxExpansionTerms:
      typeof queryExpansion.maxExpansionTerms === 'number' &&
      Number.isFinite(queryExpansion.maxExpansionTerms) &&
      queryExpansion.maxExpansionTerms > 0
        ? normalizeLimit(queryExpansion.maxExpansionTerms)
        : DEFAULT_QUERY_EXPANSION_MAX_TERMS,
  };
}

function buildSimilarityTokenSet(text: string): Set<string> {
  const tokens = text
    .toLowerCase()
    .split(/[^\p{L}\p{N}]+/u)
    .filter((token) => token.length >= 2);
  return new Set(tokens);
}

function normalizeExpansionCandidate(value: string | null | undefined): string | undefined {
  if (!value) {
    return undefined;
  }

  const normalized = value.replace(/[-_]+/g, ' ').trim();
  return normalized.length > 0 ? normalized : undefined;
}

async function expandQueryWithEntityGraph(
  query: string,
  config: Required<QueryExpansionConfig>
): Promise<string> {
  const normalizedQuery = query.trim().toLowerCase();
  if (normalizedQuery.length === 0) {
    return query;
  }

  const queryTokens = [...buildSimilarityTokenSet(query)].slice(0, 8);
  if (queryTokens.length === 0) {
    return query;
  }

  const conn = await getConnection();
  const params: Array<string | number> = [];
  const scoreClauses: string[] = [];
  const whereClauses: string[] = [];

  const pushScoredMatch = (expression: string, value: string, weight: number): void => {
    const paramIndex = params.push(value);
    scoreClauses.push(`CASE WHEN ${expression.replaceAll('?', `$${paramIndex}`)} THEN ${weight} ELSE 0 END`);
    whereClauses.push(expression.replaceAll('?', `$${paramIndex}`));
  };

  pushScoredMatch('LOWER(e.name) = ?', normalizedQuery, 8);
  pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) = ?", normalizedQuery, 10);
  const escapedFullQuery = `%${escapeLikePattern(normalizedQuery)}%`;
  pushScoredMatch("LOWER(e.name) LIKE ? ESCAPE '\\'", escapedFullQuery, 4);
  pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) LIKE ? ESCAPE '\\'", escapedFullQuery, 5);

  for (const token of queryTokens) {
    const escapedToken = `%${escapeLikePattern(token)}%`;
    pushScoredMatch("LOWER(e.name) LIKE ? ESCAPE '\\'", escapedToken, 2);
    pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) LIKE ? ESCAPE '\\'", escapedToken, 3);
  }

  if (whereClauses.length === 0) {
    return query;
  }

  const seedLimitParam = params.push(config.maxSeedEntities);
  const seedReader = await conn.runAndReadAll(
    `SELECT
       e.id,
       e.name,
       e.canonical_key,
       (${scoreClauses.join(' + ')}) AS match_score
     FROM entities e
     WHERE ${whereClauses.join(' OR ')}
     ORDER BY match_score DESC, e.created_at DESC
     LIMIT $${seedLimitParam}::INTEGER`,
    params
  );
  const seedRows = seedReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
    match_score: number | bigint;
  }>;

  const seedIds = seedRows
    .filter((row) => Number(row.match_score) > 0)
    .map((row) => row.id)
    .slice(0, config.maxSeedEntities);
  if (seedIds.length === 0) {
    return query;
  }

  const seedPlaceholders = seedIds.map((_, index) => `$${index + 1}`).join(',');
  const relatedLimitParam = seedIds.length + 1;
  const relationReader = await conn.runAndReadAll(
    `SELECT DISTINCT e.id, e.name, e.canonical_key
     FROM relations r
     INNER JOIN entities e
       ON (
         (r.src_id IN (${seedPlaceholders}) AND e.id = r.dst_id)
         OR
         (r.dst_id IN (${seedPlaceholders}) AND e.id = r.src_id)
       )
     WHERE e.id NOT IN (${seedPlaceholders})
     ORDER BY e.created_at DESC
     LIMIT $${relatedLimitParam}::INTEGER`,
    [...seedIds, config.maxRelatedEntities]
  );
  const relationRows = relationReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
  }>;

  const coClaimReader = await conn.runAndReadAll(
    `SELECT DISTINCT e.id, e.name, e.canonical_key
     FROM claim_entities seed
     INNER JOIN claim_entities sibling ON sibling.claim_id = seed.claim_id
     INNER JOIN entities e ON e.id = sibling.entity_id
     WHERE seed.entity_id IN (${seedPlaceholders})
       AND sibling.entity_id NOT IN (${seedPlaceholders})
     ORDER BY e.created_at DESC
     LIMIT $${relatedLimitParam}::INTEGER`,
    [...seedIds, config.maxRelatedEntities]
  );
  const coClaimRows = coClaimReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
  }>;

  const originalTerms = buildSimilarityTokenSet(query);
  const expansionTerms: string[] = [];
  const seenTerms = new Set<string>();

  for (const row of [...relationRows, ...coClaimRows]) {
    for (const candidate of [
      normalizeExpansionCandidate(row.name),
      normalizeExpansionCandidate(row.canonical_key),
    ]) {
      if (!candidate) {
        continue;
      }

      const candidateTokens = buildSimilarityTokenSet(candidate);
      const introducesNewTerm = [...candidateTokens].some((token) => !originalTerms.has(token));
      const candidateKey = candidate.toLowerCase();

      if (!introducesNewTerm || seenTerms.has(candidateKey)) {
        continue;
      }

      seenTerms.add(candidateKey);
      expansionTerms.push(candidate);

      if (expansionTerms.length >= config.maxExpansionTerms) {
        return `${query} ${expansionTerms.join(' ')}`.trim();
      }
    }
  }

  return expansionTerms.length > 0 ? `${query} ${expansionTerms.join(' ')}`.trim() : query;
}

function cosineSimilarity(a: readonly number[], b: readonly number[]): number {
  if (a.length === 0 || b.length === 0 || a.length !== b.length) {
    return 0;
  }

  let dot = 0;
  let normA = 0;
  let normB = 0;
  for (let i = 0; i < a.length; i++) {
    const av = a[i]!;
    const bv = b[i]!;
    dot += av * bv;
    normA += av * av;
    normB += bv * bv;
  }

  if (normA === 0 || normB === 0) {
    return 0;
  }

  const similarity = dot / Math.sqrt(normA * normB);
  return Math.max(0, Math.min(1, (similarity + 1) / 2));
}

function jaccardSimilarity(a: Set<string>, b: Set<string>): number {
  if (a.size === 0 || b.size === 0) {
    return 0;
  }

  let intersection = 0;
  for (const token of a) {
    if (b.has(token)) {
      intersection++;
    }
  }

  const union = a.size + b.size - intersection;
  return union === 0 ? 0 : intersection / union;
}

async function fetchClaimEmbeddings(
  claimIds: readonly string[]
): Promise<Map<string, readonly number[]>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT claim_id, embedding FROM claim_vectors WHERE claim_id IN (${placeholders})`,
    [...claimIds]
  );
  const rows = reader.getRowObjects() as unknown as Array<{
    claim_id: string;
    embedding: number[];
  }>;

  return new Map(
    rows.map((row) => [
      row.claim_id,
      Array.isArray(row.embedding) ? row.embedding.map((value) => Number(value)) : [],
    ])
  );
}

function candidateSimilarity(
  candidate: RankedSearchResult,
  selected: RankedSearchResult,
  embeddings: Map<string, readonly number[]>,
  tokenSets: Map<string, Set<string>>
): number {
  const candidateEmbedding = embeddings.get(candidate.claim.id);
  const selectedEmbedding = embeddings.get(selected.claim.id);
  const vectorSimilarity =
    candidateEmbedding && selectedEmbedding
      ? cosineSimilarity(candidateEmbedding, selectedEmbedding)
      : 0;

  const candidateTokens =
    tokenSets.get(candidate.claim.id) ?? buildSimilarityTokenSet(candidate.claim.text);
  const selectedTokens =
    tokenSets.get(selected.claim.id) ?? buildSimilarityTokenSet(selected.claim.text);

  tokenSets.set(candidate.claim.id, candidateTokens);
  tokenSets.set(selected.claim.id, selectedTokens);

  return Math.max(vectorSimilarity, jaccardSimilarity(candidateTokens, selectedTokens));
}

function rerankWithMmr(
  results: RankedSearchResult[],
  mmrConfig: Required<MmrConfig>,
  limit: number,
  embeddings: Map<string, readonly number[]>
): RankedSearchResult[] {
  if (results.length <= 1) {
    return results;
  }

  const headSize = Math.min(results.length, Math.max(limit, mmrConfig.maxCandidates));
  const head = results.slice(0, headSize);
  const tail = results.slice(headSize);

  const minScore = Math.min(...head.map((result) => result.fusedScore));
  const maxScore = Math.max(...head.map((result) => result.fusedScore));
  const scoreSpan = Math.max(maxScore - minScore, 0.000001);
  const relevance = new Map(
    head.map((result) => [result.claim.id, (result.fusedScore - minScore) / scoreSpan])
  );
  const tokenSets = new Map<string, Set<string>>();
  const selected: RankedSearchResult[] = [];
  const remaining = [...head];

  while (remaining.length > 0) {
    let bestIndex = 0;
    let bestScore = Number.NEGATIVE_INFINITY;

    for (let i = 0; i < remaining.length; i++) {
      const candidate = remaining[i]!;
      const relevanceScore = relevance.get(candidate.claim.id) ?? 0;
      const redundancyPenalty =
        selected.length === 0
          ? 0
          : Math.max(
              ...selected.map((chosen) =>
                candidateSimilarity(candidate, chosen, embeddings, tokenSets)
              )
            );
      const mmrScore =
        mmrConfig.lambda * relevanceScore - (1 - mmrConfig.lambda) * redundancyPenalty;

      if (
        mmrScore > bestScore ||
        (mmrScore === bestScore &&
          candidate.fusedScore > (remaining[bestIndex]?.fusedScore ?? Number.NEGATIVE_INFINITY))
      ) {
        bestIndex = i;
        bestScore = mmrScore;
      }
    }

    selected.push(remaining.splice(bestIndex, 1)[0]!);
  }

  return [...selected, ...tail];
}

/**
 * ページネーション付き検索結果
 * exactOptionalPropertyTypes対応: next_cursorはundefinedも許容
 */
export interface PaginatedSearchResult {
  /** スコア付きClaim配列 */
  results: ScoredClaim[];
  /** 次ページのカーソル（最後のclaim_id、ない場合はundefined）*/
  next_cursor: string | undefined;
  /** さらに結果があるか */
  has_more: boolean;
  /** 総件数（概算、limitまでの取得数） */
  total_in_page: number;
}

// ========== グローバル設定 ==========

/** グローバルEmbeddingService（index.tsから初期化） */
let globalEmbeddingService: EmbeddingService | null = null;

/**
 * EmbeddingServiceを設定
 * MCP server初期化時に呼び出す
 */
export function setEmbeddingService(service: EmbeddingService): void {
  globalEmbeddingService = service;
}

/**
 * EmbeddingServiceを取得
 */
export function getEmbeddingService(): EmbeddingService | null {
  return globalEmbeddingService;
}

// ========== Text検索 ==========

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
    },
    score: row.text_score,
  }));
}

// ========== Vector検索 ==========

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
  validateEmbedding(queryEmbedding);

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
    },
    score: row.vec_score,
  }));
}

// ========== 結果マージ ==========

/**
 * テキストとベクトル検索結果をマージ
 * TLA+ C_Merge: FULL OUTER JOIN相当
 *
 * @param textResults テキスト検索結果
 * @param vecResults ベクトル検索結果
 * @param alpha ベクトル重み
 * @param threshold 閾値
 * @returns 融合スコア付きClaim配列
 */
function mergeResults(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  alpha: number,
  threshold: number
): { claim: Claim; fusedScore: number }[] {
  // ClaimIdでマップ化
  const textMap = new Map<string, SearchResult>();
  for (const r of textResults) {
    textMap.set(r.claim.id, r);
  }

  const vecMap = new Map<string, SearchResult>();
  for (const r of vecResults) {
    vecMap.set(r.claim.id, r);
  }

  // 全候補のIDを収集（UNION）
  // TLA+ Inv_C_MergeComplete: C_merged = C_textCandidates ∪ C_vecCandidates
  const allIds = new Set([...textMap.keys(), ...vecMap.keys()]);

  const merged: { claim: Claim; fusedScore: number }[] = [];

  for (const id of allIds) {
    const textResult = textMap.get(id);
    const vecResult = vecMap.get(id);

    // 少なくとも一方には存在（UNIONなので）
    const claim = textResult?.claim ?? vecResult?.claim;
    if (!claim) continue;

    // スコア取得（存在しない方は0）
    const textScore = textResult?.score ?? 0;
    const vecScore = vecResult?.score ?? 0;

    // TLA+ FusedScore: α × vecScore + (1-α) × textScore
    const fusedScore = alpha * vecScore + (1 - alpha) * textScore;

    // TLA+ Inv_C_ThresholdFiltering: score >= threshold
    if (fusedScore >= threshold) {
      merged.push({ claim, fusedScore });
    }
  }

  // スコア降順ソート
  merged.sort((a, b) => b.fusedScore - a.fusedScore);

  return merged;
}

// ========== g()再ランキング用ヘルパー ==========

/**
 * utility統計情報を取得（z-score計算用）
 * @param scopes 検索対象スコープ
 * @returns mean, std（stdが0の場合は1.0を返す）
 */
async function getClaimStats(
  scopes: string[],
  filters: ClaimSearchFilters = {}
): Promise<UtilityStats> {
  if (scopes.length === 0) {
    return { mean: 0, std: 1 };
  }

  const conn = await getConnection();
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(',');
  const filterConditions = buildClaimFilterConditions('c', filters, scopes.length + 1);

  const sql = `
    SELECT
      AVG(utility) as mean,
      COALESCE(NULLIF(STDDEV_SAMP(utility), 0), 1.0) as std
    FROM claims c
    WHERE c.scope IN (${scopePlaceholders})
      AND ${activeClaimFilter('c')}
      ${filterConditions.sql ? `AND ${filterConditions.sql}` : ''}
  `;

  const reader = await conn.runAndReadAll(sql, [...scopes, ...filterConditions.params]);
  const rows = reader.getRowObjects() as unknown as { mean: number | null; std: number }[];
  const row = rows[0];

  if (!row || row.mean === null) {
    return { mean: 0, std: 1 };
  }

  return { mean: row.mean, std: row.std };
}

/**
 * Claimメトリクスを取得
 * @param claimIds 取得対象のClaim ID配列
 * @returns ClaimIdをキーとするメトリクスマップ
 */
async function fetchClaimMetrics(claimIds: string[]): Promise<Map<string, ClaimMetrics>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, i) => `$${i + 1}`).join(',');

  // recency計算にはrecency_anchorを使用（positive feedbackでのみ更新される）
  const sql = `
    SELECT
      c.id,
      c.utility,
      c.confidence,
      c.kind,
      COALESCE(c.recency_anchor, c.created_at) as ts_eff,
      COUNT(DISTINCT e.id) as evidence_count,
      CASE
        WHEN COALESCE(json_extract_string(c.provenance, '$.actor'), '') <> ''
         AND COALESCE(json_extract_string(c.provenance, '$.note'), '') <> ''
        THEN 1
        ELSE 0
      END as has_provenance_actor_note,
      MAX(CASE WHEN pq.id IS NOT NULL THEN 1 ELSE 0 END) as has_promotion_lineage
    FROM claims c
    LEFT JOIN evidence e ON e.claim_id = c.id
    LEFT JOIN promotion_queue pq
      ON pq.accepted_claim_id = c.id
     AND pq.status = 'accepted'
    WHERE c.id IN (${placeholders}) AND ${activeClaimFilter('c')}
    GROUP BY
      c.id,
      c.utility,
      c.confidence,
      c.kind,
      COALESCE(c.recency_anchor, c.created_at),
      c.provenance
  `;

  const reader = await conn.runAndReadAll(sql, claimIds);
  const rawRows = reader.getRowObjects() as unknown as ClaimMetricsRow[];
  const rows = normalizeRowsTimestamps(rawRows);

  const metricsMap = new Map<string, ClaimMetrics>();
  for (const row of rows) {
    metricsMap.set(row.id, {
      id: row.id,
      utility: row.utility,
      confidence: row.confidence,
      ts_eff: row.ts_eff,
      kind: row.kind,
      evidence_count: Number(row.evidence_count),
      has_provenance_actor_note: Number(row.has_provenance_actor_note) > 0,
      has_promotion_lineage: Number(row.has_promotion_lineage) > 0,
    });
  }

  return metricsMap;
}

/**
 * g()適用版マージ関数
 * TLA+ Inv_RangeBounds: g ∈ [0.09, 1.0]
 *
 * @param textResults テキスト検索結果
 * @param vecResults ベクトル検索結果
 * @param claimMetrics Claimメトリクスマップ
 * @param stats utility統計情報
 * @param alpha ベクトル重み
 * @param threshold 閾値
 * @param includeBreakdown スコア内訳を含めるか
 * @returns g()適用済み検索結果
 */
function mergeResultsWithRerank(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  claimMetrics: Map<string, ClaimMetrics>,
  stats: UtilityStats,
  alpha: number,
  threshold: number,
  includeBreakdown: boolean = false,
  intent?: ActivateIntent
): RankedSearchResult[] {
  // ClaimIdでマップ化
  const textMap = new Map<string, SearchResult>();
  for (const r of textResults) {
    textMap.set(r.claim.id, r);
  }

  const vecMap = new Map<string, SearchResult>();
  for (const r of vecResults) {
    vecMap.set(r.claim.id, r);
  }

  // 全候補のIDを収集（UNION）
  const allIds = new Set([...textMap.keys(), ...vecMap.keys()]);

  const merged: RankedSearchResult[] = [];

  for (const id of allIds) {
    const textResult = textMap.get(id);
    const vecResult = vecMap.get(id);

    const claim = textResult?.claim ?? vecResult?.claim;
    if (!claim) continue;

    // スコア取得
    const textScore = textResult?.score ?? 0;
    const vecScore = vecResult?.score ?? 0;

    // メトリクス取得（存在しない場合はデフォルト値）
    const metrics = claimMetrics.get(id);
    let gFactor: GFactorBreakdown;
    let intentBreakdown: ReturnType<typeof calculateIntentScoreBreakdown> = undefined;
    let provenanceQuality = undefined;

    if (metrics) {
      const baseGFactor = calculateGFromClaim(
        metrics.utility,
        metrics.confidence,
        metrics.ts_eff,
        metrics.kind,
        stats
      );
      intentBreakdown = calculateIntentScoreBreakdown(
        intent,
        metrics.kind,
        claim.memory_type ?? null
      );
      const adjustedRecencyTerm = intentBreakdown
        ? adjustRecencyTerm(baseGFactor.recency_term, intentBreakdown.recency_weight)
        : baseGFactor.recency_term;

      gFactor = {
        ...baseGFactor,
        recency_term: adjustedRecencyTerm,
        g: baseGFactor.utility_term * baseGFactor.confidence_term * adjustedRecencyTerm,
      };
      provenanceQuality = calculateProvenanceQualityBreakdown({
        evidenceCount: metrics.evidence_count,
        hasProvenanceActorNote: metrics.has_provenance_actor_note,
        hasPromotionLineage: metrics.has_promotion_lineage,
      });
    } else {
      // メトリクスがない場合: g = 1.0（影響なし）
      gFactor = {
        utility_term: 1.0,
        confidence_term: 1.0,
        recency_term: 1.0,
        g: 1.0,
      };
    }

    const breakdown = calculateScoreBreakdown(
      textScore,
      vecScore,
      alpha,
      gFactor,
      intentBreakdown,
      provenanceQuality
    );
    const scoreFinal = breakdown.score_final;

    if (scoreFinal >= threshold) {
      const result: RankedSearchResult = { claim, fusedScore: scoreFinal };

      if (includeBreakdown) {
        result.breakdown = breakdown;
      }

      merged.push(result);
    }
  }

  // スコア降順ソート
  merged.sort((a, b) => b.fusedScore - a.fusedScore);

  return merged;
}

// ========== Hybrid Search メイン ==========

/**
 * ハイブリッド検索
 * ADR-0004 設計C: テキスト+ベクトル融合検索
 *
 * 処理フロー:
 * 1. クエリ埋め込み生成（失敗時: Text-onlyフォールバック）
 * 2. 並列検索: Promise.all([textSearch, vectorSearch])
 * 3. 結果マージ: FULL OUTER JOIN
 * 4. スコア融合: hybrid_score(text, vec, α)
 * 5. 閾値フィルタ: score >= 0.15
 * 6. ランキング: ORDER BY score DESC LIMIT k
 *
 * TLA+ 活性性質:
 * - Liveness_EventuallyDone: async/awaitで完了保証
 * - Liveness_C_MergeEventuallyComplete: Promise.all()で並列実行
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（オプション）
 * @returns Claim配列
 */
export async function hybridSearch(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<Claim[]> {
  const results = await hybridSearchWithScores(scopes, limit, query, config);
  return results.map((result) => result.claim);
}

/**
 * スコア付きハイブリッド検索
 * hybridSearchと同じロジックだが、fusedScoreも返す
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（オプション）
 * @returns ScoredClaim配列（claim + score）
 */
export async function hybridSearchWithScores(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<ScoredClaim[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  const normalizedLimit = normalizeLimit(limit);
  const alpha = resolveAlpha(config?.alpha);
  const threshold = resolveThreshold(config?.threshold);
  const kText = resolveCandidateLimit(config?.kText, K_TEXT);
  const kVec = resolveCandidateLimit(config?.kVec, K_VEC);
  const mmrConfig = resolveMmrConfig(config?.mmr);
  const queryExpansionConfig = resolveQueryExpansionConfig(config?.queryExpansion);
  const embeddingService = config?.embeddingService ?? globalEmbeddingService;
  const includeBreakdown = config?.includeBreakdown ?? false;
  const enableRerank = config?.enableRerank ?? true;
  const filters: ClaimSearchFilters = {
    ...(config?.boundaryClasses ? { boundaryClasses: config.boundaryClasses } : {}),
    ...(config?.kindFilter ? { kindFilter: config.kindFilter } : {}),
    ...(config?.memoryTypeFilter ? { memoryTypeFilter: config.memoryTypeFilter } : {}),
    ...(config?.excludedWorkingStateStatuses
      ? { excludedWorkingStateStatuses: config.excludedWorkingStateStatuses }
      : {}),
  };
  const rawQuery = query?.trim() ?? '';
  const hasQuery = rawQuery.length > 0;
  const effectiveQuery =
    hasQuery && queryExpansionConfig ? await expandQueryWithEntityGraph(rawQuery, queryExpansionConfig) : rawQuery;
  const textOnlyThreshold = hasQuery ? threshold : Number.NEGATIVE_INFINITY;
  const querylessUnlimited = !hasQuery && limit >= Number.MAX_SAFE_INTEGER / 2;

  // Step 1: クエリ埋め込み生成
  let queryEmbedding: readonly number[] | null = null;

  if (hasQuery && embeddingService) {
    const embedResult = await embeddingService.embed({
      text: effectiveQuery,
      sensitivity: 'internal',
    })();

    if (E.isRight(embedResult)) {
      queryEmbedding = embedResult.right.embedding;
    }
  }

  // Step 2: 並列検索実行
  if (queryEmbedding) {
    const [textResults, vecResults] = await Promise.all([
      textSearch(effectiveQuery, scopes, kText, filters),
      vectorSearch(queryEmbedding, scopes, kVec, filters),
    ]);

    // Step 3-5: マージ + 融合 + フィルタ + ソート
    let merged: RankedSearchResult[];

    if (enableRerank) {
      const allClaimIds = [
        ...textResults.map((r) => r.claim.id),
        ...vecResults.map((r) => r.claim.id),
      ];
      const uniqueIds = [...new Set(allClaimIds)];

      const [stats, claimMetrics] = await Promise.all([
        getClaimStats(scopes, filters),
        fetchClaimMetrics(uniqueIds),
      ]);

      merged = mergeResultsWithRerank(
        textResults,
        vecResults,
        claimMetrics,
        stats,
        alpha,
        threshold,
        includeBreakdown,
        config?.intent
      );
    } else {
      merged = mergeResults(textResults, vecResults, alpha, threshold);
    }

    if (mmrConfig && hasQuery) {
      const mmrCandidateIds = merged
        .slice(0, Math.max(normalizedLimit, mmrConfig.maxCandidates))
        .map((result) => result.claim.id);
      const embeddings = await fetchClaimEmbeddings(mmrCandidateIds);
      merged = rerankWithMmr(merged, mmrConfig, normalizedLimit, embeddings);
    }

    // Step 6: 上位k件を返却（スコア付き）
    return merged.slice(0, normalizedLimit).map((r) => ({
      claim: r.claim,
      score: r.fusedScore,
      source_layer: mapScopeToLayer(r.claim.scope),
      ...(r.breakdown ? { score_breakdown: r.breakdown } : {}),
    }));
  }

  const textResults = hasQuery
    ? await textSearch(effectiveQuery, scopes, kText, filters)
    : await fallbackToTextOnlyResults(
        scopes,
        querylessUnlimited ? undefined : normalizedLimit,
        filters
      );

  const shouldIntentRerank = enableRerank && Boolean(config?.intent);
  if (shouldIntentRerank) {
    const uniqueIds = [...new Set(textResults.map((result) => result.claim.id))];
    const [stats, claimMetrics] = await Promise.all([
      getClaimStats(scopes, filters),
      fetchClaimMetrics(uniqueIds),
    ]);

    const merged = mergeResultsWithRerank(
      textResults,
      [],
      claimMetrics,
      stats,
      0,
      textOnlyThreshold,
      includeBreakdown,
      config?.intent
    );

    const reranked = mmrConfig && hasQuery
      ? rerankWithMmr(
          merged,
          mmrConfig,
          normalizedLimit,
          await fetchClaimEmbeddings(
            merged
              .slice(0, Math.max(normalizedLimit, mmrConfig.maxCandidates))
              .map((result) => result.claim.id)
          )
        )
      : merged;

    return reranked.slice(0, normalizedLimit).map((r) => ({
      claim: r.claim,
      score: r.fusedScore,
      source_layer: mapScopeToLayer(r.claim.scope),
      ...(r.breakdown ? { score_breakdown: r.breakdown } : {}),
    }));
  }

  const textOnlyRanked: RankedSearchResult[] = textResults
    .filter((result) => result.score >= textOnlyThreshold)
    .map((result) => ({
      claim: result.claim,
      fusedScore: result.score,
      ...(includeBreakdown ? { breakdown: buildTextOnlyScoreBreakdown(result.score) } : {}),
    }));

  const diversifiedTextOnly =
    mmrConfig && hasQuery
      ? rerankWithMmr(
          textOnlyRanked,
          mmrConfig,
          normalizedLimit,
          await fetchClaimEmbeddings(
            textOnlyRanked
              .slice(0, Math.max(normalizedLimit, mmrConfig.maxCandidates))
              .map((result) => result.claim.id)
          )
        )
      : textOnlyRanked;

  return diversifiedTextOnly.slice(0, normalizedLimit).map((result) => ({
    claim: result.claim,
    score: result.fusedScore,
    source_layer: mapScopeToLayer(result.claim.scope),
    ...(result.breakdown ? { score_breakdown: result.breakdown } : {}),
  }));
}

/**
 * ページネーション付きハイブリッド検索
 * mcp-tools.md §2.1, §2.2 cursor/next_cursor/has_more対応
 * 実際のfusedScoreを返す改善版
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（cursor含む）
 * @returns ページネーション付き結果（スコア付き）
 */
export async function hybridSearchPaginated(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<PaginatedSearchResult> {
  const cursor = config?.cursor;
  const isQueryless = !query || query.trim().length === 0;

  // カーソル指定時はランキング済み候補全体から位置を特定する必要がある。
  // limit+1件だけでは2ページ目以降の has_more が誤るため、候補プール全体を取得する。
  const fetchLimit = cursor ? Number.MAX_SAFE_INTEGER : limit + 1;

  const allResults =
    cursor && isQueryless
      ? await hybridSearchWithScores(scopes, Number.MAX_SAFE_INTEGER, undefined, config)
      : await hybridSearchWithScores(scopes, fetchLimit, query, config);

  // カーソル以降のデータをフィルタ
  let filteredResults = allResults;
  if (cursor) {
    const cursorIndex = allResults.findIndex((r) => r.claim.id === cursor);
    if (cursorIndex >= 0) {
      // カーソルの次から取得
      filteredResults = allResults.slice(cursorIndex + 1);
    }
  }

  // has_more判定とlimit適用
  const has_more = filteredResults.length > limit;
  const results = filteredResults.slice(0, limit);

  // 次カーソル（最後のclaim_id）
  const next_cursor =
    has_more && results.length > 0 ? results[results.length - 1]!.claim.id : undefined;

  return {
    results,
    next_cursor,
    has_more,
    total_in_page: results.length,
  };
}

/**
 * クエリなしの場合のフォールバック
 * criticスコアでソートして返す（既存listClaimsByScopeと同等）
 */
async function fallbackToTextOnlyResults(
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
    },
    score: row.score,
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
  validateEmbedding(embedding);

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

/**
 * Claimの埋め込みベクトルを削除
 *
 * @param claimId Claim ID
 */
export async function deleteClaimVector(claimId: string): Promise<void> {
  const conn = await getConnection();
  await conn.run('DELETE FROM claim_vectors WHERE claim_id = $1', [claimId]);
}

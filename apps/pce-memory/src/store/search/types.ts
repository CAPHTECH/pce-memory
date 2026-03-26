/**
 * Hybrid Search shared types, constants, and utilities
 * @see docs/adr/0004-hybrid-search-design.md
 */

import type { Claim } from '../claims.js';
import type { EmbeddingService } from '@pce/embeddings';
import type { FeedbackBoostOptions, GFactorBreakdown, ScoreBreakdown } from '../rerank.js';
import type { ActivateIntent, ClaimKind, ClaimStatus, MemoryType } from '../../domain/types.js';
import type { ClaimLinkType } from '../claimLinks.js';

// ========== ADR-0004 パラメータ ==========

/** ベクトル検索重み（TLA+ Alpha = 65 / 100） */
export const ALPHA = 0.65;

/** 採用閾値（TLA+ Threshold = 15 / 100） */
export const THRESHOLD = 0.15;

/** テキスト検索上限（8× of k_final） */
export const K_TEXT = 128;

/** ベクトル検索上限（16× of k_final） */
export const K_VEC = 256;

/** MMR関連デフォルト値 */
export const DEFAULT_MMR_LAMBDA = 0.72;
export const DEFAULT_MMR_MAX_CANDIDATES = 48;

/** Query expansion関連デフォルト値 */
export const DEFAULT_QUERY_EXPANSION_MAX_SEED_ENTITIES = 3;
export const DEFAULT_QUERY_EXPANSION_MAX_RELATED_ENTITIES = 8;
export const DEFAULT_QUERY_EXPANSION_MAX_TERMS = 6;

/** Topology walk関連デフォルト値 */
export const DEFAULT_TOPOLOGY_SEED_K = 6;
export const DEFAULT_TOPOLOGY_MAX_HOPS = 2;
export const DEFAULT_TOPOLOGY_HOP_DECAY = 0.75;
export const DEFAULT_TOPOLOGY_ENTITY_PATH_WEIGHT = 0.45;
export const DEFAULT_TOPOLOGY_ENTITY_PATH_CONFIDENCE = 1.0;

/** criticスコアが存在しない場合のデフォルト値 */
export const DEFAULT_CRITIC_SCORE = 0.5;

/** 最小limit値 */
export const MIN_LIMIT = 1;

// ========== 型定義 ==========

/**
 * 検索結果（スコア付き）
 * TLA+: [claim: ClaimId, score: Score]
 */
export interface SearchResult {
  claim: Claim;
  score: number;
}

export interface ClaimSearchFilters {
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

export type TopologyEdgeDirection = 'forward' | 'both';
export type TopologyEdgeAction = 'boost' | 'flag_conflict' | 'shadow_old';

export interface TopologyEdgePolicyEntry {
  weight?: number;
  direction?: TopologyEdgeDirection;
  action?: TopologyEdgeAction;
}

export interface TopologyConfig {
  enabled?: boolean;
  mode?: 'walk';
  seedK?: number;
  maxHops?: number;
  hopDecay?: number;
  includePaths?: boolean;
  edgePolicy?: Partial<Record<ClaimLinkType, TopologyEdgePolicyEntry>>;
}

export interface ResolvedTopologyConfig {
  enabled: boolean;
  mode: 'walk';
  seedK: number;
  maxHops: number;
  hopDecay: number;
  includePaths: boolean;
  entityPathWeight: number;
  entityPathConfidence: number;
  edgePolicy: Record<
    ClaimLinkType,
    {
      weight: number;
      direction: TopologyEdgeDirection;
      action: TopologyEdgeAction;
    }
  >;
}

export interface FeedbackBoostConfig extends FeedbackBoostOptions {
  enabled?: boolean;
}

/**
 * g()再ランキング用メトリクス
 */
export interface ClaimMetrics {
  id: string;
  utility: number;
  confidence: number;
  /** 有効タイムスタンプ（updated_at or created_at） */
  ts_eff: Date | string;
  kind: string;
  evidence_count: number;
  has_provenance_actor_note: boolean;
  has_promotion_lineage: boolean;
  helpful_feedback_count: number;
  harmful_feedback_count: number;
  outdated_feedback_count: number;
  duplicate_feedback_count: number;
}

/**
 * utility統計情報（z-score計算用）
 */
export interface UtilityStats {
  mean: number;
  std: number;
}

export interface ClaimMetricsRow {
  id: string;
  utility: number;
  confidence: number;
  ts_eff: Date | string;
  kind: string;
  evidence_count: number | bigint;
  has_provenance_actor_note: number | bigint | boolean;
  has_promotion_lineage: number | bigint | boolean;
  helpful_feedback_count: number | bigint;
  harmful_feedback_count: number | bigint;
  outdated_feedback_count: number | bigint;
  duplicate_feedback_count: number | bigint;
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
  /** 実験的なgraph topology walk設定 */
  topology?: TopologyConfig;
  /** 実験的なfeedback boost設定 */
  feedbackBoost?: FeedbackBoostConfig;
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

export interface SimilarClaimMatch {
  id: string;
  similarity: number;
  text_preview: string;
  created_at: string;
}

export interface NewerSimilarClaimMatch {
  freshness: 'stale_candidate';
  newer_similar: string;
  similarity: number;
  created_at: string;
}

export interface SimilarClaimRow {
  id: string;
  similarity: number;
  text: string;
  created_at: Date | string;
}

export interface NewerSimilarClaimRow {
  claim_id: string;
  newer_similar: string;
  similarity: number;
  newer_created_at: Date | string;
  newer_vector_rowid?: number | bigint;
}

// ========== ユーティリティ関数 ==========

export function activeClaimFilter(alias: string): string {
  return `COALESCE(${alias}.tombstone, FALSE) = FALSE
    AND NOT EXISTS (
      SELECT 1
      FROM promotion_queue pq
      WHERE pq.accepted_claim_id = ${alias}.id
        AND pq.status = 'rolled_back'
    )`;
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
export function normalizeLimit(limit: number): number {
  const floored = Math.floor(limit);
  return Number.isFinite(floored) ? Math.max(MIN_LIMIT, floored) : MIN_LIMIT;
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

export function buildClaimFilterConditions(
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

export function mapScopeToLayer(scope: string): 'micro' | 'meso' | 'macro' {
  if (scope === 'principle') {
    return 'macro';
  }
  if (scope === 'project') {
    return 'meso';
  }
  return 'micro';
}

export function buildTextOnlyScoreBreakdown(score: number): ScoreBreakdown {
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

export const NEUTRAL_G_FACTOR: GFactorBreakdown = {
  utility_term: 1.0,
  confidence_term: 1.0,
  recency_term: 1.0,
  g: 1.0,
};

export function resolveAlpha(alpha: number | undefined): number {
  return typeof alpha === 'number' && Number.isFinite(alpha) ? alpha : ALPHA;
}

export function resolveThreshold(threshold: number | undefined): number {
  return typeof threshold === 'number' && Number.isFinite(threshold) ? threshold : THRESHOLD;
}

export function resolveCandidateLimit(limit: number | undefined, fallback: number): number {
  return typeof limit === 'number' && Number.isFinite(limit) && limit > 0
    ? normalizeLimit(limit)
    : fallback;
}

export function resolveMmrConfig(mmr: MmrConfig | undefined): Required<MmrConfig> | undefined {
  if (!mmr?.enabled) {
    return undefined;
  }

  const lambda =
    typeof mmr.lambda === 'number' &&
    Number.isFinite(mmr.lambda) &&
    mmr.lambda > 0 &&
    mmr.lambda < 1
      ? mmr.lambda
      : DEFAULT_MMR_LAMBDA;

  const maxCandidates =
    typeof mmr.maxCandidates === 'number' &&
    Number.isFinite(mmr.maxCandidates) &&
    mmr.maxCandidates > 0
      ? normalizeLimit(mmr.maxCandidates)
      : DEFAULT_MMR_MAX_CANDIDATES;

  return {
    enabled: true,
    lambda,
    maxCandidates,
  };
}

export function resolveQueryExpansionConfig(
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

export function resolveFeedbackBoostConfig(
  feedbackBoost: FeedbackBoostConfig | undefined
): FeedbackBoostOptions | undefined {
  if (!feedbackBoost?.enabled) {
    return undefined;
  }

  return {
    ...(typeof feedbackBoost.helpfulWeight === 'number'
      ? { helpfulWeight: feedbackBoost.helpfulWeight }
      : {}),
    ...(typeof feedbackBoost.harmfulWeight === 'number'
      ? { harmfulWeight: feedbackBoost.harmfulWeight }
      : {}),
    ...(typeof feedbackBoost.outdatedWeight === 'number'
      ? { outdatedWeight: feedbackBoost.outdatedWeight }
      : {}),
    ...(typeof feedbackBoost.duplicateWeight === 'number'
      ? { duplicateWeight: feedbackBoost.duplicateWeight }
      : {}),
    ...(typeof feedbackBoost.minMultiplier === 'number'
      ? { minMultiplier: feedbackBoost.minMultiplier }
      : {}),
    ...(typeof feedbackBoost.maxMultiplier === 'number'
      ? { maxMultiplier: feedbackBoost.maxMultiplier }
      : {}),
  };
}

export function resolveTopologyConfig(
  topology: TopologyConfig | undefined
): ResolvedTopologyConfig | undefined {
  if (topology?.enabled === false) {
    return undefined;
  }

  const maxHops =
    typeof topology?.maxHops === 'number' &&
    Number.isFinite(topology.maxHops) &&
    topology.maxHops > 0
      ? Math.min(DEFAULT_TOPOLOGY_MAX_HOPS, normalizeLimit(topology.maxHops))
      : DEFAULT_TOPOLOGY_MAX_HOPS;

  const hopDecay =
    typeof topology?.hopDecay === 'number' &&
    Number.isFinite(topology.hopDecay) &&
    topology.hopDecay > 0 &&
    topology.hopDecay <= 1
      ? topology.hopDecay
      : DEFAULT_TOPOLOGY_HOP_DECAY;

  const defaultEdgePolicy: ResolvedTopologyConfig['edgePolicy'] = {
    supports: { weight: 0.9, direction: 'forward', action: 'boost' },
    extends: { weight: 0.7, direction: 'forward', action: 'boost' },
    related: { weight: 0.35, direction: 'both', action: 'boost' },
    contradicts: { weight: 0.15, direction: 'both', action: 'flag_conflict' },
    supersedes: { weight: 1.0, direction: 'forward', action: 'shadow_old' },
  };

  const resolvedEdgePolicy = (Object.keys(defaultEdgePolicy) as ClaimLinkType[]).reduce<
    ResolvedTopologyConfig['edgePolicy']
  >((acc, linkType) => {
    const override = topology?.edgePolicy?.[linkType];
    const defaultEntry = defaultEdgePolicy[linkType];
    acc[linkType] = {
      weight:
        typeof override?.weight === 'number' &&
        Number.isFinite(override.weight) &&
        override.weight >= 0
          ? override.weight
          : defaultEntry.weight,
      direction:
        override?.direction === 'both' || override?.direction === 'forward'
          ? override.direction
          : defaultEntry.direction,
      action:
        override?.action === 'flag_conflict' ||
        override?.action === 'shadow_old' ||
        override?.action === 'boost'
          ? override.action
          : defaultEntry.action,
    };
    return acc;
  }, {} as ResolvedTopologyConfig['edgePolicy']);

  return {
    enabled: true,
    mode: 'walk',
    seedK:
      typeof topology?.seedK === 'number' && Number.isFinite(topology.seedK) && topology.seedK > 0
        ? normalizeLimit(topology.seedK)
        : DEFAULT_TOPOLOGY_SEED_K,
    maxHops,
    hopDecay,
    includePaths: topology?.includePaths !== false,
    entityPathWeight: DEFAULT_TOPOLOGY_ENTITY_PATH_WEIGHT,
    entityPathConfidence: DEFAULT_TOPOLOGY_ENTITY_PATH_CONFIDENCE,
    edgePolicy: resolvedEdgePolicy,
  };
}

export function buildSimilarityTokenSet(text: string): Set<string> {
  const tokens = text
    .toLowerCase()
    .split(/[^\p{L}\p{N}]+/u)
    .filter((token) => token.length >= 2);
  return new Set(tokens);
}

export function buildTextPreview(text: string, maxLength: number = 120): string {
  const normalized = text.replace(/\s+/g, ' ').trim();
  if (normalized.length <= maxLength) {
    return normalized;
  }
  return `${normalized.slice(0, Math.max(0, maxLength - 3))}...`;
}

export function normalizeSimilarity(value: unknown): number {
  const similarity = Number(value);
  return Number.isFinite(similarity) ? similarity : 0;
}

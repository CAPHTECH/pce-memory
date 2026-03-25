/**
 * Hybrid Search実装（ADR-0004 設計C準拠）
 *
 * Thin facade that composes the search pipeline modules.
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
 * - k_text = 128: テキスト検索上限（8× k_final）
 * - k_vec = 256: ベクトル検索上限（16× k_final）
 *
 * @see docs/adr/0004-hybrid-search-design.md
 * @see docs/spec/tlaplus/hybrid_search_simple.tla
 */

import type { EmbeddingService } from '@pce/embeddings';
import type { Claim } from './claims.js';
import * as E from 'fp-ts/Either';
import { calculateScoreBreakdown, calculateUsageTermBreakdown } from './rerank.js';
import {
  type ClaimSearchFilters,
  type HybridSearchConfig,
  type RankedSearchResult,
  type ScoredClaim,
  type PaginatedSearchResult,
  NEUTRAL_G_FACTOR,
  K_TEXT,
  K_VEC,
  normalizeLimit,
  resolveAlpha,
  resolveThreshold,
  resolveCandidateLimit,
  resolveMmrConfig,
  resolveQueryExpansionConfig,
  resolveFeedbackBoostConfig,
  mapScopeToLayer,
  buildTextOnlyScoreBreakdown,
} from './search/types.js';
import { textSearch, fallbackToTextOnlyResults } from './search/textSearch.js';
import { vectorSearch } from './search/vectorSearch.js';
import {
  mergeResults,
  mergeResultsWithRerank,
  getClaimStats,
  fetchClaimMetrics,
} from './search/mergeAndRerank.js';
import { rerankWithMmr, fetchClaimEmbeddings } from './search/mmr.js';
import { expandQueryWithEntityGraph } from './search/queryExpansion.js';
import { paginateResults } from './search/pagination.js';

// ========== Re-exports (backward compatibility) ==========

export type {
  MmrConfig,
  QueryExpansionConfig,
  FeedbackBoostConfig,
  RankedSearchResult,
  HybridSearchConfig,
  ScoredClaim,
  PaginatedSearchResult,
  SimilarClaimMatch,
  NewerSimilarClaimMatch,
} from './search/types.js';

export { escapeLikePattern, splitQueryWords, buildWordOrCondition } from './search/types.js';
export { textSearch } from './search/textSearch.js';
export {
  vectorSearch,
  saveClaimVector,
  getClaimVector,
  findSimilarActiveClaims,
  findNewerSimilarClaims,
  deleteClaimVector,
} from './search/vectorSearch.js';

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
  const feedbackBoostConfig = resolveFeedbackBoostConfig(config?.feedbackBoost);
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
    hasQuery && queryExpansionConfig
      ? await expandQueryWithEntityGraph(rawQuery, queryExpansionConfig)
      : rawQuery;
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
        config?.intent,
        feedbackBoostConfig
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

  const shouldTextOnlyRerank =
    enableRerank && (Boolean(config?.intent) || feedbackBoostConfig !== undefined);
  if (shouldTextOnlyRerank) {
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
      config?.intent,
      feedbackBoostConfig
    );

    const reranked =
      mmrConfig && hasQuery
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

  if (enableRerank) {
    const usageAwareRanked: RankedSearchResult[] = textResults
      .filter((result) => result.score >= textOnlyThreshold)
      .map((result) => {
        const usageTerm = calculateUsageTermBreakdown({
          retrievalCount: result.claim.retrieval_count,
          lastRetrievedAt: result.claim.last_retrieved_at ?? null,
          createdAt: result.claim.created_at,
        });
        const breakdown = calculateScoreBreakdown(
          result.score,
          0,
          0,
          NEUTRAL_G_FACTOR,
          undefined,
          undefined,
          undefined,
          usageTerm
        );

        return {
          claim: result.claim,
          fusedScore: breakdown.score_final,
          ...(includeBreakdown ? { breakdown } : {}),
        };
      });

    const diversifiedUsageAware =
      mmrConfig && hasQuery
        ? rerankWithMmr(
            usageAwareRanked,
            mmrConfig,
            normalizedLimit,
            await fetchClaimEmbeddings(
              usageAwareRanked
                .slice(0, Math.max(normalizedLimit, mmrConfig.maxCandidates))
                .map((result) => result.claim.id)
            )
          )
        : usageAwareRanked;

    return diversifiedUsageAware.slice(0, normalizedLimit).map((result) => ({
      claim: result.claim,
      score: result.fusedScore,
      source_layer: mapScopeToLayer(result.claim.scope),
      ...(result.breakdown ? { score_breakdown: result.breakdown } : {}),
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

  return paginateResults(allResults, cursor, limit);
}

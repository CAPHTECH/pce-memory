/**
 * Score fusion + g() rerank integration
 * @see docs/adr/0004-hybrid-search-design.md
 */

import { getConnection } from '../../db/connection.js';
import {
  adjustRecencyTerm,
  calculateFeedbackBoostBreakdown,
  calculateGFromClaim,
  calculateIntentScoreBreakdown,
  calculateProvenanceQualityBreakdown,
  calculateScoreBreakdown,
  calculateUsageTermBreakdown,
  type FeedbackBoostOptions,
} from '../rerank.js';
import { normalizeRowsTimestamps } from '../../utils/serialization.js';
import type { ActivateIntent } from '../../domain/types.js';
import {
  type SearchResult,
  type ClaimSearchFilters,
  type ClaimMetrics,
  type ClaimMetricsRow,
  type UtilityStats,
  type RankedSearchResult,
  activeClaimFilter,
  buildClaimFilterConditions,
} from './types.js';

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
export function mergeResults(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  alpha: number,
  threshold: number
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
  // TLA+ Inv_C_MergeComplete: C_merged = C_textCandidates ∪ C_vecCandidates
  const allIds = new Set([...textMap.keys(), ...vecMap.keys()]);

  const merged: RankedSearchResult[] = [];

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

/**
 * utility統計情報を取得（z-score計算用）
 * @param scopes 検索対象スコープ
 * @returns mean, std（stdが0の場合は1.0を返す）
 */
export async function getClaimStats(
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
export async function fetchClaimMetrics(claimIds: string[]): Promise<Map<string, ClaimMetrics>> {
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
      MAX(CASE WHEN pq.id IS NOT NULL THEN 1 ELSE 0 END) as has_promotion_lineage,
      COALESCE(fb.helpful_feedback_count, 0) as helpful_feedback_count,
      COALESCE(fb.harmful_feedback_count, 0) as harmful_feedback_count,
      COALESCE(fb.outdated_feedback_count, 0) as outdated_feedback_count,
      COALESCE(fb.duplicate_feedback_count, 0) as duplicate_feedback_count
    FROM claims c
    LEFT JOIN evidence e ON e.claim_id = c.id
    LEFT JOIN promotion_queue pq
      ON pq.accepted_claim_id = c.id
     AND pq.status = 'accepted'
    LEFT JOIN (
      SELECT
        claim_id,
        SUM(CASE WHEN signal = 'helpful' THEN 1 ELSE 0 END) as helpful_feedback_count,
        SUM(CASE WHEN signal = 'harmful' THEN 1 ELSE 0 END) as harmful_feedback_count,
        SUM(CASE WHEN signal = 'outdated' THEN 1 ELSE 0 END) as outdated_feedback_count,
        SUM(CASE WHEN signal = 'duplicate' THEN 1 ELSE 0 END) as duplicate_feedback_count
      FROM feedback
      GROUP BY claim_id
    ) fb ON fb.claim_id = c.id
    WHERE c.id IN (${placeholders}) AND ${activeClaimFilter('c')}
    GROUP BY
      c.id,
      c.utility,
      c.confidence,
      c.kind,
      COALESCE(c.recency_anchor, c.created_at),
      c.provenance,
      fb.helpful_feedback_count,
      fb.harmful_feedback_count,
      fb.outdated_feedback_count,
      fb.duplicate_feedback_count
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
      helpful_feedback_count: Number(row.helpful_feedback_count),
      harmful_feedback_count: Number(row.harmful_feedback_count),
      outdated_feedback_count: Number(row.outdated_feedback_count),
      duplicate_feedback_count: Number(row.duplicate_feedback_count),
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
export function mergeResultsWithRerank(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  claimMetrics: Map<string, ClaimMetrics>,
  stats: UtilityStats,
  alpha: number,
  threshold: number,
  includeBreakdown: boolean = false,
  intent?: ActivateIntent,
  feedbackBoostConfig?: FeedbackBoostOptions
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
    const usageTerm = calculateUsageTermBreakdown({
      retrievalCount: claim.retrieval_count,
      lastRetrievedAt: claim.last_retrieved_at ?? null,
      createdAt: claim.created_at,
    });
    let gFactor: { utility_term: number; confidence_term: number; recency_term: number; g: number };
    let intentBreakdown: ReturnType<typeof calculateIntentScoreBreakdown> = undefined;
    let provenanceQuality = undefined;
    let feedbackBoost = undefined;

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
      feedbackBoost = feedbackBoostConfig
        ? calculateFeedbackBoostBreakdown(
            {
              helpful: metrics.helpful_feedback_count,
              harmful: metrics.harmful_feedback_count,
              outdated: metrics.outdated_feedback_count,
              duplicate: metrics.duplicate_feedback_count,
            },
            feedbackBoostConfig
          )
        : undefined;
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
      provenanceQuality,
      feedbackBoost,
      usageTerm
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

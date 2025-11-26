/**
 * g()再ランキング関数 - 純粋TypeScript実装
 * activation-ranking.md仕様に準拠
 *
 * TLA+ Invariants:
 * - Inv_RangeBounds: g ∈ [0.09, 1.0]
 * - Inv_UtilityMonotonicity: utility増加 → g増加
 * - Inv_RecencyMonotonicity: 時間経過 → recency減少 → g減少
 */

/** Kind別半減期（日） */
export const KIND_HALF_LIVES: Record<string, number> = {
  fact: 120,
  task: 14,
  preference: 90,
  policy_hint: 365,
};
export const DEFAULT_HALF_LIFE = 30;

/** g()係数の内訳（デバッグ・分析用） */
export interface GFactorBreakdown {
  /** utility項: 0.6 + 0.4σ(z) ∈ [0.6, 1.0] */
  utility_term: number;
  /** confidence項: 0.5 + 0.5c ∈ [0.5, 1.0] */
  confidence_term: number;
  /** recency項: 0.3 + 0.7r ∈ [0.3, 1.0] */
  recency_term: number;
  /** g = utility_term × confidence_term × recency_term ∈ [0.09, 1.0] */
  g: number;
}

/** Hybrid Searchスコアの完全内訳 */
export interface ScoreBreakdown {
  /** テキスト検索スコア */
  s_text: number;
  /** ベクトル検索スコア */
  s_vec: number;
  /** 融合スコア: S = α × s_vec + (1-α) × s_text */
  S: number;
  /** g()係数の内訳 */
  g: GFactorBreakdown;
  /** 最終スコア: score_final = S × g */
  score_final: number;
}

/**
 * シグモイド関数
 * σ(x) = 1 / (1 + e^(-x))
 * 範囲: (0, 1), σ(0) = 0.5
 */
export function sigmoid(x: number): number {
  return 1.0 / (1.0 + Math.exp(-x));
}

/**
 * recency decay関数
 * 指数減衰: exp(-ln(2) × age_days / half_life)
 *
 * @param ts - タイムスタンプ（Date or ISO string）
 * @param halfLifeDays - 半減期（日）
 * @returns 減衰係数 ∈ [0, 1]（不正日付は0、未来日付は1）
 */
export function recencyDecay(ts: Date | string, halfLifeDays: number): number {
  const timestamp = ts instanceof Date ? ts : new Date(ts);
  const timestampMs = timestamp.getTime();

  // Invalid date check（NaN伝播防止）
  if (!Number.isFinite(timestampMs)) {
    return 0; // 安全側に倒す（最古扱い）
  }

  const ageDays = (Date.now() - timestampMs) / (1000 * 60 * 60 * 24);

  // 未来日付クランプ（ageDays < 0 → recency > 1 防止）
  const clampedAge = Math.max(0, ageDays);

  // ln(2) ≈ 0.693147
  return Math.exp(-0.693147 * clampedAge / halfLifeDays);
}

/**
 * Kind別の半減期を取得
 */
export function getHalfLife(kind: string): number {
  return KIND_HALF_LIVES[kind] ?? DEFAULT_HALF_LIFE;
}

/**
 * g()再ランク係数を計算
 *
 * g = (0.6 + 0.4σ(utility_z)) × (0.5 + 0.5c) × (0.3 + 0.7r)
 *
 * @param utilityZ - utility の z-score（標準化値）
 * @param confidence - 信頼度 ∈ [0, 1]
 * @param recency - recency decay値 ∈ [0, 1]
 * @returns g()係数の内訳
 */
export function calculateG(
  utilityZ: number,
  confidence: number,
  recency: number,
): GFactorBreakdown {
  // utility項: 0.6 + 0.4σ(z) ∈ [0.6, 1.0]
  const utility_term = 0.6 + 0.4 * sigmoid(utilityZ);

  // confidence項: 0.5 + 0.5c ∈ [0.5, 1.0]（クランプ済み）
  const confidence_term = 0.5 + 0.5 * Math.max(0, Math.min(1, confidence));

  // recency項: 0.3 + 0.7r ∈ [0.3, 1.0]（クランプ済み）
  const recency_term = 0.3 + 0.7 * Math.max(0, Math.min(1, recency));

  return {
    utility_term,
    confidence_term,
    recency_term,
    g: utility_term * confidence_term * recency_term,
  };
}

/**
 * Claimメトリクスからg()を計算
 *
 * @param utility - 生のutility値
 * @param confidence - 信頼度 ∈ [0, 1]
 * @param ts - タイムスタンプ（updated_at or created_at）
 * @param kind - Claimの種類（half-life決定用）
 * @param stats - utility統計（z-score計算用）
 * @returns g()係数の内訳
 */
export function calculateGFromClaim(
  utility: number,
  confidence: number,
  ts: Date | string,
  kind: string,
  stats: { mean: number; std: number },
): GFactorBreakdown {
  // utility z-score: (utility - mean) / std
  // ゼロ除算防御: std=0の場合はε(0.001)を使用してz≈0に近づける
  const safeStd = Math.max(stats.std, 0.001);
  const utilityZ = (utility - stats.mean) / safeStd;

  // kind別half-life
  const halfLife = getHalfLife(kind);

  // recency decay
  const recency = recencyDecay(ts, halfLife);

  return calculateG(utilityZ, confidence, recency);
}

/**
 * 完全なスコア内訳を計算
 *
 * @param textScore - テキスト検索スコア
 * @param vecScore - ベクトル検索スコア
 * @param alpha - 融合係数（デフォルト: 0.65）
 * @param gFactor - g()係数の内訳
 * @returns 完全なスコア内訳
 */
export function calculateScoreBreakdown(
  textScore: number,
  vecScore: number,
  alpha: number,
  gFactor: GFactorBreakdown,
): ScoreBreakdown {
  const S = alpha * vecScore + (1 - alpha) * textScore;
  return {
    s_text: textScore,
    s_vec: vecScore,
    S,
    g: gFactor,
    score_final: S * gFactor.g,
  };
}

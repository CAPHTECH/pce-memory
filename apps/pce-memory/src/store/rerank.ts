/**
 * g()再ランキング関数 - 純粋TypeScript実装
 * activation-ranking.md仕様に準拠
 *
 * TLA+ Invariants:
 * - Inv_RangeBounds: g ∈ [0.09, 1.0]
 * - Inv_UtilityMonotonicity: utility増加 → g増加
 * - Inv_RecencyMonotonicity: 時間経過 → recency減少 → g減少
 */
import type { ActivateIntent, ClaimKind, MemoryType } from '../domain/types.js';

/** Kind別半減期（日） */
export const KIND_HALF_LIVES = {
  fact: 120,
  task: 14,
  preference: 90,
  policy_hint: 365,
} satisfies Record<ClaimKind, number>;
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

/** Intent由来の調整内訳 */
export interface IntentScoreBreakdown {
  intent: ActivateIntent;
  kind_boost: number;
  memory_type_boost: number;
  penalty_multiplier: number;
  recency_weight: number;
  boost: number;
}

/** Provenance/evidence由来の品質補正 */
export interface ProvenanceQualityBreakdown {
  evidence_count: number;
  evidence_boost: number;
  has_actor_note: boolean;
  provenance_boost: number;
  has_promotion_lineage: boolean;
  promotion_lineage_boost: number;
  multiplier: number;
}

export interface FeedbackSignalCounts {
  helpful: number;
  harmful: number;
  outdated: number;
  duplicate: number;
}

export interface FeedbackBoostOptions {
  helpfulWeight?: number;
  harmfulWeight?: number;
  outdatedWeight?: number;
  duplicateWeight?: number;
  minMultiplier?: number;
  maxMultiplier?: number;
}

export interface FeedbackBoostBreakdown extends FeedbackSignalCounts {
  helpful_weight: number;
  harmful_weight: number;
  outdated_weight: number;
  duplicate_weight: number;
  signal_score: number;
  multiplier: number;
}

export interface UsageTermBreakdown {
  retrieval_count: number;
  usage_anchor_source: 'last_retrieved_at' | 'created_at';
  usage_anchor_at: string;
  days_since_anchor: number;
  usage_decay: number;
  retrieval_boost: number;
  multiplier: number;
}

export interface TopologyPathSegmentBreakdown {
  kind: 'claim_link' | 'entity_relation';
  from_claim_id: string;
  to_claim_id: string;
  weight: number;
  confidence: number;
  link_id?: string;
  link_type?: string;
  relation_id?: string;
  relation_type?: string;
  relation_direction?: 'forward' | 'reverse';
  via_entity_ids?: string[];
}

export interface TopologyScoreBreakdown {
  seed_claim_id: string;
  kind: 'support' | 'conflict' | 'supersession';
  depth: number;
  hop_decay: number;
  multiplier: number;
  path_score: number;
  shadowed_claim_ids?: string[];
  path?: TopologyPathSegmentBreakdown[];
  conflicts?: Array<{
    claim_id: string;
    link_type: string;
    via_claim_id: string;
  }>;
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
  /** intent-aware補正 */
  intent?: IntentScoreBreakdown;
  /** provenance/evidence品質補正 */
  provenance_quality?: ProvenanceQualityBreakdown;
  /** feedback由来の品質補正 */
  feedback_boost?: FeedbackBoostBreakdown;
  /** activate使用履歴由来の品質補正 */
  usage_term?: UsageTermBreakdown;
  /** graph topology由来の補正 */
  topology?: TopologyScoreBreakdown;
  /** 最終スコア: score_final = S × g × intent_boost × provenance_quality × feedback_boost × usage_term */
  score_final: number;
}

type IntentProfile = {
  recencyWeight: number;
  kindBoosts: Partial<Record<ClaimKind, number>>;
  memoryTypeBoosts: Partial<Record<MemoryType, number>>;
};

const DEFAULT_INTENT_PROFILE: IntentProfile = {
  recencyWeight: 1.0,
  kindBoosts: {},
  memoryTypeBoosts: {},
};
const DEFAULT_FEEDBACK_BOOST_OPTIONS: Required<FeedbackBoostOptions> = {
  helpfulWeight: 0.25,
  harmfulWeight: 0.35,
  outdatedWeight: 0.18,
  duplicateWeight: 0.12,
  minMultiplier: 0.45,
  maxMultiplier: 1.65,
};
const POLICY_CHECK_ACTIVE_TASK_PENALTY = 0.1;
export const USAGE_HALF_LIFE_DAYS = 30;
export const USAGE_DECAY_FACTOR = 0.5;
export const MIN_USAGE_DECAY = 0.5;
export const RETRIEVAL_BOOST_WEIGHT = 0.1;
export const MAX_RETRIEVAL_BOOST = 2.0;
export const MIN_RETRIEVAL_COUNT_FOR_BOOST = 10;
const DAY_IN_MS = 1000 * 60 * 60 * 24;

const INTENT_PROFILES: Record<ActivateIntent, IntentProfile> = {
  resume_task: {
    recencyWeight: 1.6,
    kindBoosts: { task: 1.3 },
    memoryTypeBoosts: { working_state: 1.35, knowledge: 1.05 },
  },
  debug_incident: {
    recencyWeight: 1.8,
    kindBoosts: {},
    memoryTypeBoosts: { evidence: 1.4, knowledge: 1.1, procedure: 1.05 },
  },
  design_decision: {
    recencyWeight: 0.65,
    kindBoosts: {},
    memoryTypeBoosts: { knowledge: 1.2, norm: 1.2, procedure: 1.1 },
  },
  policy_check: {
    recencyWeight: 0.25,
    kindBoosts: { policy_hint: 1.2 },
    memoryTypeBoosts: { norm: 1.4, knowledge: 1.05 },
  },
};

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

  // halfLifeDaysが0以下やNaNの場合は安全側に倒す
  if (!Number.isFinite(halfLifeDays) || halfLifeDays <= 0) {
    return 0;
  }

  // ln(2) ≈ 0.693147
  return Math.exp((-0.693147 * clampedAge) / halfLifeDays);
}

/**
 * Kind別の半減期を取得
 */
export function getHalfLife(kind: string): number {
  return kind in KIND_HALF_LIVES ? KIND_HALF_LIVES[kind as ClaimKind] : DEFAULT_HALF_LIFE;
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
  recency: number
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

function clamp(value: number, min: number, max: number): number {
  return Math.min(max, Math.max(min, value));
}

function toTimestampMs(value: Date | string | null | undefined): number | undefined {
  if (value === null || value === undefined) {
    return undefined;
  }

  const timestamp = value instanceof Date ? value : new Date(value);
  const timestampMs = timestamp.getTime();
  return Number.isFinite(timestampMs) ? timestampMs : undefined;
}

export function calculateUsageTermBreakdown(input: {
  retrievalCount: number;
  lastRetrievedAt?: Date | string | null;
  createdAt: Date | string;
  nowMs?: number;
  usageHalfLifeDays?: number;
  decayFactor?: number;
  minDecay?: number;
  boostWeight?: number;
  maxBoost?: number;
  minCountForBoost?: number;
}): UsageTermBreakdown {
  const nowMs =
    typeof input.nowMs === 'number' && Number.isFinite(input.nowMs) ? input.nowMs : Date.now();
  const usageHalfLifeDays =
    typeof input.usageHalfLifeDays === 'number' &&
    Number.isFinite(input.usageHalfLifeDays) &&
    input.usageHalfLifeDays > 0
      ? input.usageHalfLifeDays
      : USAGE_HALF_LIFE_DAYS;
  const decayFactor =
    typeof input.decayFactor === 'number' && Number.isFinite(input.decayFactor)
      ? input.decayFactor
      : USAGE_DECAY_FACTOR;
  const minDecay =
    typeof input.minDecay === 'number' && Number.isFinite(input.minDecay)
      ? input.minDecay
      : MIN_USAGE_DECAY;
  const boostWeight =
    typeof input.boostWeight === 'number' && Number.isFinite(input.boostWeight)
      ? input.boostWeight
      : RETRIEVAL_BOOST_WEIGHT;
  const maxBoost =
    typeof input.maxBoost === 'number' && Number.isFinite(input.maxBoost)
      ? input.maxBoost
      : MAX_RETRIEVAL_BOOST;
  const minCountForBoost =
    typeof input.minCountForBoost === 'number' &&
    Number.isFinite(input.minCountForBoost) &&
    input.minCountForBoost >= 0
      ? Math.floor(input.minCountForBoost)
      : MIN_RETRIEVAL_COUNT_FOR_BOOST;
  const retrievalCount =
    Number.isFinite(input.retrievalCount) && input.retrievalCount > 0
      ? Math.floor(input.retrievalCount)
      : 0;

  const lastRetrievedAtMs = toTimestampMs(input.lastRetrievedAt ?? null);
  const createdAtMs = toTimestampMs(input.createdAt);
  const usageAnchorMs = lastRetrievedAtMs ?? createdAtMs ?? nowMs;
  const usage_anchor_source = lastRetrievedAtMs !== undefined ? 'last_retrieved_at' : 'created_at';
  const days_since_anchor = Math.max(0, (nowMs - usageAnchorMs) / DAY_IN_MS);
  const usage_decay =
    lastRetrievedAtMs !== undefined
      ? clamp(1.0 - (days_since_anchor / usageHalfLifeDays) * decayFactor, minDecay, 1.0)
      : 1.0;
  // Only apply boost when retrieval count exceeds the minimum threshold.
  // This prevents a feedback loop where a single accidental retrieval
  // permanently boosts a claim above more relevant results.
  const effectiveCount = retrievalCount >= minCountForBoost ? retrievalCount : 0;
  const retrieval_boost = clamp(1.0 + Math.log2(effectiveCount + 1) * boostWeight, 1.0, maxBoost);

  return {
    retrieval_count: retrievalCount,
    usage_anchor_source,
    usage_anchor_at: new Date(usageAnchorMs).toISOString(),
    days_since_anchor,
    usage_decay,
    retrieval_boost,
    multiplier: usage_decay * retrieval_boost,
  };
}

function normalizedRecencyTerm(recencyTerm: number): number {
  return clamp((recencyTerm - 0.3) / 0.7, 0, 1);
}

export function adjustRecencyTerm(recencyTerm: number, recencyWeight: number): number {
  const safeWeight = Number.isFinite(recencyWeight) && recencyWeight > 0 ? recencyWeight : 1.0;
  const normalized = normalizedRecencyTerm(recencyTerm);
  const adjusted = Math.pow(normalized, safeWeight);
  return 0.3 + 0.7 * adjusted;
}

export function calculateIntentScoreBreakdown(
  intent: ActivateIntent | undefined,
  kind: string,
  memoryType?: MemoryType | null
): IntentScoreBreakdown | undefined {
  if (!intent) {
    return undefined;
  }

  const profile = INTENT_PROFILES[intent] ?? DEFAULT_INTENT_PROFILE;
  const typedKind = kind as ClaimKind;
  const kind_boost = profile.kindBoosts[typedKind] ?? 1.0;
  const memory_type_boost = memoryType ? (profile.memoryTypeBoosts[memoryType] ?? 1.0) : 1.0;
  const penalty_multiplier =
    intent === 'policy_check' && (typedKind === 'task' || memoryType === 'working_state')
      ? POLICY_CHECK_ACTIVE_TASK_PENALTY
      : 1.0;

  return {
    intent,
    kind_boost,
    memory_type_boost,
    penalty_multiplier,
    recency_weight: profile.recencyWeight,
    boost: kind_boost * memory_type_boost * penalty_multiplier,
  };
}

export function calculateProvenanceQualityBreakdown(input: {
  evidenceCount: number;
  hasProvenanceActorNote: boolean;
  hasPromotionLineage: boolean;
}): ProvenanceQualityBreakdown {
  const evidence_count =
    Number.isFinite(input.evidenceCount) && input.evidenceCount > 0 ? input.evidenceCount : 0;
  const evidence_boost = evidence_count > 0 ? 1.1 : 1.0;
  const has_actor_note = input.hasProvenanceActorNote;
  const provenance_boost = has_actor_note ? 1.05 : 1.0;
  const has_promotion_lineage = input.hasPromotionLineage;
  const promotion_lineage_boost = has_promotion_lineage ? 1.05 : 1.0;

  return {
    evidence_count,
    evidence_boost,
    has_actor_note,
    provenance_boost,
    has_promotion_lineage,
    promotion_lineage_boost,
    multiplier: evidence_boost * provenance_boost * promotion_lineage_boost,
  };
}

export function calculateFeedbackBoostBreakdown(
  counts: FeedbackSignalCounts,
  options: FeedbackBoostOptions = {}
): FeedbackBoostBreakdown {
  const resolved: Required<FeedbackBoostOptions> = {
    helpfulWeight:
      typeof options.helpfulWeight === 'number' && Number.isFinite(options.helpfulWeight)
        ? options.helpfulWeight
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.helpfulWeight,
    harmfulWeight:
      typeof options.harmfulWeight === 'number' && Number.isFinite(options.harmfulWeight)
        ? options.harmfulWeight
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.harmfulWeight,
    outdatedWeight:
      typeof options.outdatedWeight === 'number' && Number.isFinite(options.outdatedWeight)
        ? options.outdatedWeight
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.outdatedWeight,
    duplicateWeight:
      typeof options.duplicateWeight === 'number' && Number.isFinite(options.duplicateWeight)
        ? options.duplicateWeight
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.duplicateWeight,
    minMultiplier:
      typeof options.minMultiplier === 'number' && Number.isFinite(options.minMultiplier)
        ? options.minMultiplier
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.minMultiplier,
    maxMultiplier:
      typeof options.maxMultiplier === 'number' && Number.isFinite(options.maxMultiplier)
        ? options.maxMultiplier
        : DEFAULT_FEEDBACK_BOOST_OPTIONS.maxMultiplier,
  };

  const helpful = Number.isFinite(counts.helpful) && counts.helpful > 0 ? counts.helpful : 0;
  const harmful = Number.isFinite(counts.harmful) && counts.harmful > 0 ? counts.harmful : 0;
  const outdated = Number.isFinite(counts.outdated) && counts.outdated > 0 ? counts.outdated : 0;
  const duplicate =
    Number.isFinite(counts.duplicate) && counts.duplicate > 0 ? counts.duplicate : 0;

  const signal_score =
    resolved.helpfulWeight * Math.log1p(helpful) -
    resolved.harmfulWeight * Math.log1p(harmful) -
    resolved.outdatedWeight * Math.log1p(outdated) -
    resolved.duplicateWeight * Math.log1p(duplicate);

  return {
    helpful,
    harmful,
    outdated,
    duplicate,
    helpful_weight: resolved.helpfulWeight,
    harmful_weight: resolved.harmfulWeight,
    outdated_weight: resolved.outdatedWeight,
    duplicate_weight: resolved.duplicateWeight,
    signal_score,
    multiplier: clamp(Math.exp(signal_score), resolved.minMultiplier, resolved.maxMultiplier),
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
  stats: { mean: number; std: number }
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
  intent?: IntentScoreBreakdown,
  provenanceQuality?: ProvenanceQualityBreakdown,
  feedbackBoost?: FeedbackBoostBreakdown,
  usageTerm?: UsageTermBreakdown
): ScoreBreakdown {
  const S = alpha * vecScore + (1 - alpha) * textScore;
  return {
    s_text: textScore,
    s_vec: vecScore,
    S,
    g: gFactor,
    ...(intent ? { intent } : {}),
    ...(provenanceQuality ? { provenance_quality: provenanceQuality } : {}),
    ...(feedbackBoost ? { feedback_boost: feedbackBoost } : {}),
    ...(usageTerm ? { usage_term: usageTerm } : {}),
    score_final:
      S *
      gFactor.g *
      (intent?.boost ?? 1.0) *
      (provenanceQuality?.multiplier ?? 1.0) *
      (feedbackBoost?.multiplier ?? 1.0) *
      (usageTerm?.multiplier ?? 1.0),
  };
}

/**
 * g()再ランキング関数 単体テスト
 * activation-ranking.md仕様に準拠
 *
 * TLA+ Invariants検証:
 * - Inv_RangeBounds: g ∈ [0.09, 1.0]
 * - Inv_UtilityMonotonicity: utility増加 → g増加
 * - Inv_RecencyMonotonicity: 時間経過 → recency減少 → g減少
 */
import { describe, it, expect } from "vitest";
import {
  sigmoid,
  recencyDecay,
  calculateG,
  calculateGFromClaim,
  getHalfLife,
  KIND_HALF_LIVES,
  DEFAULT_HALF_LIFE,
  calculateScoreBreakdown,
} from "../src/store/rerank.js";

describe("sigmoid function", () => {
  it("σ(0) = 0.5", () => {
    expect(sigmoid(0)).toBeCloseTo(0.5, 10);
  });

  it("σ(x) approaches 1 for large positive x", () => {
    expect(sigmoid(10)).toBeGreaterThan(0.9999);
    expect(sigmoid(10)).toBeLessThanOrEqual(1.0);
  });

  it("σ(x) approaches 0 for large negative x", () => {
    expect(sigmoid(-10)).toBeLessThan(0.0001);
    expect(sigmoid(-10)).toBeGreaterThanOrEqual(0.0);
  });

  it("σ(-x) + σ(x) = 1 (symmetry)", () => {
    const x = 2.5;
    expect(sigmoid(-x) + sigmoid(x)).toBeCloseTo(1.0, 10);
  });

  it("σ is monotonically increasing", () => {
    const values = [-5, -2, 0, 2, 5];
    for (let i = 0; i < values.length - 1; i++) {
      expect(sigmoid(values[i])).toBeLessThan(sigmoid(values[i + 1]));
    }
  });
});

describe("recencyDecay function", () => {
  it("decay = 1.0 at t=0 (now)", () => {
    const now = new Date();
    expect(recencyDecay(now, 30)).toBeCloseTo(1.0, 5);
  });

  it("decay ≈ 0.5 at half-life", () => {
    const halfLife = 30;
    const past = new Date(Date.now() - halfLife * 24 * 60 * 60 * 1000);
    expect(recencyDecay(past, halfLife)).toBeCloseTo(0.5, 2);
  });

  it("decay ≈ 0.25 at 2x half-life", () => {
    const halfLife = 30;
    const past = new Date(Date.now() - 2 * halfLife * 24 * 60 * 60 * 1000);
    expect(recencyDecay(past, halfLife)).toBeCloseTo(0.25, 2);
  });

  it("decay is monotonically decreasing with age", () => {
    const halfLife = 30;
    const decays = [0, 10, 30, 60, 90].map((days) => {
      const past = new Date(Date.now() - days * 24 * 60 * 60 * 1000);
      return recencyDecay(past, halfLife);
    });

    for (let i = 0; i < decays.length - 1; i++) {
      expect(decays[i]).toBeGreaterThan(decays[i + 1]);
    }
  });

  it("accepts ISO string timestamp", () => {
    const now = new Date().toISOString();
    expect(recencyDecay(now, 30)).toBeCloseTo(1.0, 5);
  });
});

describe("getHalfLife function", () => {
  it("returns correct half-life for fact", () => {
    expect(getHalfLife("fact")).toBe(120);
  });

  it("returns correct half-life for task", () => {
    expect(getHalfLife("task")).toBe(14);
  });

  it("returns correct half-life for preference", () => {
    expect(getHalfLife("preference")).toBe(90);
  });

  it("returns correct half-life for policy_hint", () => {
    expect(getHalfLife("policy_hint")).toBe(365);
  });

  it("returns default half-life for unknown kind", () => {
    expect(getHalfLife("unknown")).toBe(DEFAULT_HALF_LIFE);
    expect(getHalfLife("")).toBe(DEFAULT_HALF_LIFE);
  });
});

describe("calculateG function", () => {
  it("returns g in [0.09, 1.0] for extreme inputs", () => {
    // 最小ケース: utility_z=-∞, confidence=0, recency=0
    const minG = calculateG(-100, 0, 0);
    expect(minG.g).toBeGreaterThanOrEqual(0.09);

    // 最大ケース: utility_z=+∞, confidence=1, recency=1
    const maxG = calculateG(100, 1, 1);
    expect(maxG.g).toBeLessThanOrEqual(1.0);
  });

  it("TLA+ Inv_RangeBounds: g ∈ [0.09, 1.0] for all valid inputs", () => {
    const testCases = [
      { utilityZ: 0, confidence: 0.5, recency: 0.5 },
      { utilityZ: -5, confidence: 0, recency: 0 },
      { utilityZ: 5, confidence: 1, recency: 1 },
      { utilityZ: -10, confidence: 0.1, recency: 0.1 },
      { utilityZ: 10, confidence: 0.9, recency: 0.9 },
    ];

    for (const tc of testCases) {
      const result = calculateG(tc.utilityZ, tc.confidence, tc.recency);
      expect(result.g).toBeGreaterThanOrEqual(0.09);
      expect(result.g).toBeLessThanOrEqual(1.0);
    }
  });

  it("utility_term is in [0.6, 1.0]", () => {
    // σ(-∞) → 0, so 0.6 + 0.4*0 = 0.6
    const minUtility = calculateG(-100, 0.5, 0.5);
    expect(minUtility.utility_term).toBeCloseTo(0.6, 2);

    // σ(+∞) → 1, so 0.6 + 0.4*1 = 1.0
    const maxUtility = calculateG(100, 0.5, 0.5);
    expect(maxUtility.utility_term).toBeCloseTo(1.0, 2);
  });

  it("confidence_term is in [0.5, 1.0]", () => {
    // c=0: 0.5 + 0.5*0 = 0.5
    const minConf = calculateG(0, 0, 0.5);
    expect(minConf.confidence_term).toBeCloseTo(0.5, 10);

    // c=1: 0.5 + 0.5*1 = 1.0
    const maxConf = calculateG(0, 1, 0.5);
    expect(maxConf.confidence_term).toBeCloseTo(1.0, 10);
  });

  it("recency_term is in [0.3, 1.0]", () => {
    // r=0: 0.3 + 0.7*0 = 0.3
    const minRecency = calculateG(0, 0.5, 0);
    expect(minRecency.recency_term).toBeCloseTo(0.3, 10);

    // r=1: 0.3 + 0.7*1 = 1.0
    const maxRecency = calculateG(0, 0.5, 1);
    expect(maxRecency.recency_term).toBeCloseTo(1.0, 10);
  });

  it("TLA+ Inv_UtilityMonotonicity: utility増加 → g増加", () => {
    const base = calculateG(0, 0.5, 0.5);
    const higher = calculateG(2, 0.5, 0.5);
    expect(higher.g).toBeGreaterThan(base.g);
  });

  it("confidence増加 → g増加", () => {
    const low = calculateG(0, 0.3, 0.5);
    const high = calculateG(0, 0.8, 0.5);
    expect(high.g).toBeGreaterThan(low.g);
  });

  it("recency増加 → g増加", () => {
    const old = calculateG(0, 0.5, 0.2);
    const recent = calculateG(0, 0.5, 0.9);
    expect(recent.g).toBeGreaterThan(old.g);
  });

  it("clamps confidence to [0, 1]", () => {
    const belowZero = calculateG(0, -0.5, 0.5);
    const aboveOne = calculateG(0, 1.5, 0.5);

    expect(belowZero.confidence_term).toBeCloseTo(0.5, 10); // 0.5 + 0.5*0
    expect(aboveOne.confidence_term).toBeCloseTo(1.0, 10); // 0.5 + 0.5*1
  });

  it("clamps recency to [0, 1]", () => {
    const belowZero = calculateG(0, 0.5, -0.5);
    const aboveOne = calculateG(0, 0.5, 1.5);

    expect(belowZero.recency_term).toBeCloseTo(0.3, 10); // 0.3 + 0.7*0
    expect(aboveOne.recency_term).toBeCloseTo(1.0, 10); // 0.3 + 0.7*1
  });
});

describe("calculateGFromClaim function", () => {
  it("calculates g with default stats", () => {
    const now = new Date();
    const stats = { mean: 0, std: 1 };

    const result = calculateGFromClaim(0, 0.5, now, "fact", stats);
    expect(result.g).toBeGreaterThan(0);
    expect(result.g).toBeLessThanOrEqual(1.0);
  });

  it("uses kind-specific half-life", () => {
    const past = new Date(Date.now() - 30 * 24 * 60 * 60 * 1000); // 30 days ago
    const stats = { mean: 0, std: 1 };

    // fact has 120 day half-life, so 30 days is ~25% through
    const factResult = calculateGFromClaim(0, 0.5, past, "fact", stats);
    // task has 14 day half-life, so 30 days is >2 half-lives
    const taskResult = calculateGFromClaim(0, 0.5, past, "task", stats);

    // fact should have higher recency_term (longer half-life)
    expect(factResult.recency_term).toBeGreaterThan(taskResult.recency_term);
  });

  it("uses z-score for utility", () => {
    const now = new Date();

    // utility = mean = 5, std = 2
    // z-score = (5 - 5) / 2 = 0
    const average = calculateGFromClaim(5, 0.5, now, "fact", { mean: 5, std: 2 });

    // utility = 9, z-score = (9 - 5) / 2 = 2 (above average)
    const aboveAvg = calculateGFromClaim(9, 0.5, now, "fact", { mean: 5, std: 2 });

    // utility = 1, z-score = (1 - 5) / 2 = -2 (below average)
    const belowAvg = calculateGFromClaim(1, 0.5, now, "fact", { mean: 5, std: 2 });

    expect(aboveAvg.g).toBeGreaterThan(average.g);
    expect(belowAvg.g).toBeLessThan(average.g);
  });
});

describe("calculateScoreBreakdown function", () => {
  it("calculates S correctly with alpha", () => {
    const gFactor = calculateG(0, 0.5, 0.5);
    const breakdown = calculateScoreBreakdown(0.4, 0.8, 0.65, gFactor);

    // S = 0.65 * 0.8 + 0.35 * 0.4 = 0.52 + 0.14 = 0.66
    expect(breakdown.S).toBeCloseTo(0.66, 10);
  });

  it("calculates score_final correctly", () => {
    const gFactor = calculateG(0, 0.5, 0.5);
    const breakdown = calculateScoreBreakdown(0.4, 0.8, 0.65, gFactor);

    expect(breakdown.score_final).toBeCloseTo(breakdown.S * gFactor.g, 10);
  });

  it("preserves individual scores in breakdown", () => {
    const gFactor = calculateG(1, 0.7, 0.8);
    const breakdown = calculateScoreBreakdown(0.3, 0.9, 0.65, gFactor);

    expect(breakdown.s_text).toBe(0.3);
    expect(breakdown.s_vec).toBe(0.9);
    expect(breakdown.g).toBe(gFactor);
  });
});

describe("KIND_HALF_LIVES constants", () => {
  it("matches spec values from activation-ranking.md", () => {
    expect(KIND_HALF_LIVES.fact).toBe(120);
    expect(KIND_HALF_LIVES.task).toBe(14);
    expect(KIND_HALF_LIVES.preference).toBe(90);
    expect(KIND_HALF_LIVES.policy_hint).toBe(365);
  });

  it("DEFAULT_HALF_LIFE is 30", () => {
    expect(DEFAULT_HALF_LIFE).toBe(30);
  });
});

describe("Edge case handling", () => {
  it("recencyDecay returns 0 for invalid date string", () => {
    expect(recencyDecay("invalid-date", 30)).toBe(0);
    expect(recencyDecay("not-a-date", 30)).toBe(0);
    expect(recencyDecay("", 30)).toBe(0);
  });

  it("recencyDecay returns 0 for invalid Date object", () => {
    expect(recencyDecay(new Date("invalid"), 30)).toBe(0);
    expect(recencyDecay(new Date(NaN), 30)).toBe(0);
  });

  it("recencyDecay clamps future dates to 1.0", () => {
    const tomorrow = new Date(Date.now() + 86400000); // 1 day in future
    expect(recencyDecay(tomorrow, 30)).toBeCloseTo(1.0, 5);
  });

  it("recencyDecay clamps far future dates to 1.0", () => {
    const farFuture = new Date(Date.now() + 365 * 86400000); // 1 year in future
    expect(recencyDecay(farFuture, 30)).toBeCloseTo(1.0, 5);
  });

  it("calculateGFromClaim handles std=0", () => {
    const now = new Date();
    const result = calculateGFromClaim(5, 0.5, now, "fact", { mean: 5, std: 0 });
    expect(Number.isFinite(result.g)).toBe(true);
    expect(result.g).toBeGreaterThanOrEqual(0.09);
    expect(result.g).toBeLessThanOrEqual(1.0);
  });

  it("calculateGFromClaim handles negative std", () => {
    const now = new Date();
    const result = calculateGFromClaim(5, 0.5, now, "fact", { mean: 5, std: -1 });
    expect(Number.isFinite(result.g)).toBe(true);
    expect(result.g).toBeGreaterThanOrEqual(0.09);
    expect(result.g).toBeLessThanOrEqual(1.0);
  });

  it("calculateGFromClaim handles very small std", () => {
    const now = new Date();
    const result = calculateGFromClaim(5, 0.5, now, "fact", { mean: 5, std: 0.0001 });
    expect(Number.isFinite(result.g)).toBe(true);
    expect(result.g).toBeGreaterThanOrEqual(0.09);
    expect(result.g).toBeLessThanOrEqual(1.0);
  });

  it("calculateG handles extreme utilityZ values", () => {
    const extreme1 = calculateG(1000, 0.5, 0.5);
    const extreme2 = calculateG(-1000, 0.5, 0.5);
    expect(Number.isFinite(extreme1.g)).toBe(true);
    expect(Number.isFinite(extreme2.g)).toBe(true);
    expect(extreme1.g).toBeLessThanOrEqual(1.0);
    expect(extreme2.g).toBeGreaterThanOrEqual(0.09);
  });
});

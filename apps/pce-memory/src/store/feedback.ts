import { getConnection } from '../db/connection.js';

export interface FeedbackInput {
  claim_id: string;
  signal: 'helpful' | 'harmful' | 'outdated' | 'duplicate';
  score?: number;
}

/**
 * Feedbackシグナル → utility/confidenceデルタ値
 * activation-ranking.md仕様に準拠
 *
 * | Signal    | utility | confidence |
 * |-----------|---------|------------|
 * | helpful   | +0.10   | +0.05      |
 * | harmful   | -0.20   | -0.10      |
 * | outdated  |  0      | -0.20      |
 * | duplicate | -0.05   |  0         |
 */
export const FEEDBACK_DELTAS: Record<
  FeedbackInput['signal'],
  { utility: number; confidence: number }
> = {
  helpful: { utility: 0.1, confidence: 0.05 },
  harmful: { utility: -0.2, confidence: -0.1 },
  outdated: { utility: 0.0, confidence: -0.2 },
  duplicate: { utility: -0.05, confidence: 0.0 },
};

/**
 * Feedbackを記録し、Claimのutility/confidenceを更新
 *
 * TLA+ Inv_RangeBounds対応:
 * - confidenceは[0, 1]にクランプ
 * - utilityは累積（上限なし）
 */
export async function recordFeedback(input: FeedbackInput): Promise<{ id: string }> {
  const conn = await getConnection();
  const id = `fb_${crypto.randomUUID().slice(0, 8)}`;

  // 1. feedbackテーブルにイベント記録
  await conn.run('INSERT INTO feedback (id, claim_id, signal, score) VALUES ($1, $2, $3, $4)', [
    id,
    input.claim_id,
    input.signal,
    input.score ?? null,
  ]);

  // 2. claimsのutility/confidence更新（g()再ランキング用）
  // positive feedback (utility > 0) のみrecency_anchorを更新
  // negative feedbackではrecency_anchorを維持（ペナルティ効果を保持）
  const deltas = FEEDBACK_DELTAS[input.signal];

  await conn.run(
    `UPDATE claims SET
      utility = utility + $1,
      confidence = GREATEST(0.0, LEAST(1.0, confidence + $2)),
      updated_at = CURRENT_TIMESTAMP,
      recency_anchor = CASE WHEN $1 > 0 THEN CURRENT_TIMESTAMP ELSE recency_anchor END
    WHERE id = $3`,
    [deltas.utility, deltas.confidence, input.claim_id]
  );

  return { id };
}

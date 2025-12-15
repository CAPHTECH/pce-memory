import { getConnection } from '../db/connection.js';

/**
 * Criticスコアを原子的に更新
 *
 * TOCTOU競合状態を回避するため、SQL UPSERTを使用。
 * criticテーブルにはFK制約がないため、ON CONFLICTは正常動作する。
 *
 * @param claimId - 対象ClaimのID
 * @param delta - スコアの増減値
 * @param min - スコアの下限
 * @param max - スコアの上限
 * @returns 更新後のスコア
 */
export async function updateCritic(
  claimId: string,
  delta: number,
  min: number,
  max: number
): Promise<number> {
  const conn = await getConnection();

  // 原子的UPSERT: INSERT時は delta をクランプ、UPDATE時は (current + delta) をクランプ
  // Note: criticテーブルにはFK制約がないため、ON CONFLICTは安全に使用可能
  const reader = await conn.runAndReadAll(
    `INSERT INTO critic (claim_id, score)
     VALUES ($1, LEAST($2::DOUBLE, GREATEST($3::DOUBLE, $4::DOUBLE)))
     ON CONFLICT (claim_id)
     DO UPDATE SET score = LEAST($2::DOUBLE, GREATEST($3::DOUBLE, critic.score + $4::DOUBLE))
     RETURNING score`,
    [claimId, max, min, delta]
  );

  const rows = reader.getRowObjects() as { score: number }[];
  return rows[0]?.score ?? 0;
}

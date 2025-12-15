import { getConnection } from '../db/connection.js';

export async function updateCritic(
  claimId: string,
  delta: number,
  min: number,
  max: number
): Promise<number> {
  const conn = await getConnection();
  // 現在のスコアを取得
  const reader = await conn.runAndReadAll('SELECT score FROM critic WHERE claim_id = $1', [
    claimId,
  ]);
  const rows = reader.getRowObjects() as { score: number }[];
  const exists = rows.length > 0;
  const current = rows[0]?.score ?? 0;
  const next = Math.min(max, Math.max(min, current + delta));

  // 分離方式のupsert（ON CONFLICT句のDuckDB互換性問題回避）
  if (exists) {
    await conn.run('UPDATE critic SET score = $1 WHERE claim_id = $2', [next, claimId]);
  } else {
    await conn.run('INSERT INTO critic (claim_id, score) VALUES ($1, $2)', [claimId, next]);
  }
  return next;
}

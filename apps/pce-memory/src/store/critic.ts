import { getConnection } from "../db/connection.js";

export async function updateCritic(claimId: string, delta: number, min: number, max: number): Promise<number> {
  const conn = await getConnection();
  // 現在のスコアを取得
  const reader = await conn.runAndReadAll(
    "SELECT score FROM critic WHERE claim_id = $1",
    [claimId]
  );
  const rows = reader.getRowObjects() as { score: number }[];
  const current = rows[0]?.score ?? 0;
  const next = Math.min(max, Math.max(min, current + delta));

  // upsert
  await conn.run(
    "INSERT INTO critic (claim_id, score) VALUES ($1, $2) ON CONFLICT(claim_id) DO UPDATE SET score=excluded.score",
    [claimId, next]
  );
  return next;
}

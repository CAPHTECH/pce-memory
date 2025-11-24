import { getDb } from "../db/connection";

export function updateCritic(claimId: string, delta: number, min: number, max: number) {
  const db = getDb().connect();
  try {
    const row = db.prepare("SELECT score FROM critic WHERE claim_id = ?").get(claimId) as { score: number } | undefined;
    const current = row?.score ?? 0;
    const next = Math.min(max, Math.max(min, current + delta));
    db.prepare("INSERT INTO critic (claim_id, score) VALUES (?, ?) ON CONFLICT(claim_id) DO UPDATE SET score=excluded.score").run(
      claimId,
      next
    );
    return next;
  } finally {
    db.close();
  }
}

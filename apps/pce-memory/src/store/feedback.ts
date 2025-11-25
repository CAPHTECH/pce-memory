import { getConnection } from "../db/connection.js";

export interface FeedbackInput {
  claim_id: string;
  signal: "helpful" | "harmful" | "outdated" | "duplicate";
  score?: number;
}

export async function recordFeedback(input: FeedbackInput): Promise<{ id: string }> {
  const conn = await getConnection();
  const id = `fb_${crypto.randomUUID().slice(0, 8)}`;
  await conn.run(
    "INSERT INTO feedback (id, claim_id, signal, score) VALUES ($1, $2, $3, $4)",
    [id, input.claim_id, input.signal, input.score ?? null]
  );
  return { id };
}

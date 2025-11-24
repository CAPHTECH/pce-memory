import { getDb } from "../db/connection";

export interface FeedbackInput {
  claim_id: string;
  signal: "helpful" | "harmful" | "outdated";
  score?: number;
}

export function recordFeedback(input: FeedbackInput) {
  const db = getDb().connect();
  try {
    const id = `fb_${crypto.randomUUID().slice(0, 8)}`;
    db.prepare("INSERT INTO feedback (id, claim_id, signal, score) VALUES (?,?,?,?)").run(
      id,
      input.claim_id,
      input.signal,
      input.score ?? null
    );
    return { id };
  } finally {
    db.close();
  }
}

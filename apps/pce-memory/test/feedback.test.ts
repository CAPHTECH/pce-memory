import { describe, it, expect, beforeEach } from "vitest";
import { initDb, initSchema, resetDb, getConnection } from "../src/db/connection";
import { upsertClaim } from "../src/store/claims";
import { recordFeedback } from "../src/store/feedback";
import { updateCritic } from "../src/store/critic";

beforeEach(async () => {
  resetDb();
  process.env.PCE_DB = ":memory:";
  await initDb();
  await initSchema();
});

describe("feedback critic update", () => {
  it("updates critic score within bounds", async () => {
    const c = await upsertClaim({
      text: "foo",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hfb",
    });
    await recordFeedback({ claim_id: c.id, signal: "helpful", score: 1 });
    const next = await updateCritic(c.id, 1, 0, 5);
    expect(next).toBeLessThanOrEqual(5);
    const conn = await getConnection();
    const reader = await conn.runAndReadAll("SELECT score FROM critic WHERE claim_id = $1", [c.id]);
    const rows = reader.getRowObjects() as { score: number }[];
    expect(rows[0].score).toBe(next);
  });
});

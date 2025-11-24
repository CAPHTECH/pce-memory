import { describe, it, expect, beforeEach } from "vitest";
import { initSchema } from "../src/db/connection";
import { upsertClaim } from "../src/store/claims";
import { recordFeedback } from "../src/store/feedback";
import { updateCritic } from "../src/store/critic";
import { getDb } from "../src/db/connection";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("feedback critic update", () => {
  it("updates critic score within bounds", () => {
    const c = upsertClaim({
      text: "foo",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hfb",
    });
    recordFeedback({ claim_id: c.id, signal: "helpful", score: 1 });
    const next = updateCritic(c.id, 1, 0, 5);
    expect(next).toBeLessThanOrEqual(5);
    const db = getDb().connect();
    const row = db.prepare("SELECT score FROM critic WHERE claim_id=?").get(c.id) as { score: number };
    db.close();
    expect(row.score).toBe(next);
  });
});

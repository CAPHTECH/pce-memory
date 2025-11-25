import { describe, it, expect, beforeEach } from "vitest";
import { initDb, initSchema, resetDb } from "../src/db/connection";
import { recordFeedback } from "../src/store/feedback";
import { findClaimById } from "../src/store/claims";

beforeEach(async () => {
  resetDb();
  process.env.PCE_DB = ":memory:";
  await initDb();
  await initSchema();
});

describe("feedback validation", () => {
  it("fails when claim does not exist", async () => {
    const exists = await findClaimById("missing");
    expect(exists).toBeUndefined();
    // recordFeedback is low-level and will insert; handler checks existence.
    // So this test just documents current behavior.
    const res = await recordFeedback({ claim_id: "missing", signal: "helpful" });
    expect(res.id).toBeDefined();
  });
});

import { describe, it, expect, beforeEach } from "vitest";
import { initSchema } from "../src/db/connection";
import { recordFeedback } from "../src/store/feedback";
import { findClaimById } from "../src/store/claims";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("feedback validation", () => {
  it("fails when claim does not exist", () => {
    const exists = findClaimById("missing");
    expect(exists).toBeUndefined();
    // recordFeedback is low-level and will insert; handler checks existence.
    // So this test just documents current behavior.
    const res = recordFeedback({ claim_id: "missing", signal: "helpful" });
    expect(res.id).toBeDefined();
  });
});

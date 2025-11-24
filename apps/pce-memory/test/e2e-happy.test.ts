import { describe, it, expect, beforeEach } from "vitest";
import { initSchema } from "../src/db/connection";
import { upsertClaim } from "../src/store/claims";
import { listClaimsByScope } from "../src/store/claims";
import { boundaryValidate } from "@pce/boundary";
import { defaultPolicy } from "@pce/policy-schemas/src/defaults";
import { recordFeedback } from "../src/store/feedback";
import { updateCritic } from "../src/store/critic";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("E2E happy path (upsert->activate->validate->feedback)", () => {
  it("runs end-to-end without errors", () => {
    // upsert
    const claim = upsertClaim({
      text: "foo",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "e2e1",
    });
    expect(claim.id).toBeDefined();

    // activate
    const claims = listClaimsByScope(["project"], 10);
    expect(claims.length).toBe(1);

    // boundary.validate
    const val = boundaryValidate({ payload: "email foo@example.com", allow: ["answer:task"], scope: "project" }, defaultPolicy.boundary);
    expect(val.allowed).toBe(true);
    expect(val.redacted).toContain("[REDACTED]");

    // feedback + critic
    recordFeedback({ claim_id: claim.id, signal: "helpful", score: 1 });
    const next = updateCritic(claim.id, 1, 0, 5);
    expect(next).toBeGreaterThan(0);
  });
});

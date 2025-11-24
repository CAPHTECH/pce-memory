import { describe, it, expect, beforeEach } from "vitest";
import { initSchema } from "../src/db/connection";
import { upsertClaim, listClaimsByScope } from "../src/store/claims";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("activate query filtering", () => {
  it("filters by scope and q substring", () => {
    upsertClaim({
      text: "foo alpha",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "q1",
    });
    upsertClaim({
      text: "beta",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "q2",
    });
    const res = listClaimsByScope(["project"], 10, "alpha");
    expect(res.map((c) => c.text)).toEqual(["foo alpha"]);
  });
});

import { describe, it, expect, beforeEach } from "vitest";
import { initSchema } from "../src/db/connection";
import { upsertClaim } from "../src/store/claims";
import { listClaimsByScope } from "../src/store/claims";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("activate validation", () => {
  it("returns validation error when scope is unknown", () => {
    const scopes = listClaimsByScope(["unknown"], 10);
    expect(scopes.length).toBe(0);
  });

  it("filters claims by scope", () => {
    upsertClaim({
      text: "a",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "h1",
    });
    upsertClaim({
      text: "b",
      kind: "fact",
      scope: "session",
      boundary_class: "internal",
      content_hash: "h2",
    });
    const scopes = listClaimsByScope(["project"], 10);
    expect(scopes.map((c) => c.scope)).toEqual(["project"]);
  });
});

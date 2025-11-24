import { describe, it, expect, beforeEach } from "vitest";
import { upsertClaim } from "../src/store/claims";
import { initSchema } from "../src/db/connection";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  initSchema();
});

describe("upsertClaim", () => {
  it("returns same id on duplicate content_hash", () => {
    const first = upsertClaim({
      text: "foo",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hash123",
    });
    const second = upsertClaim({
      text: "foo2",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hash123",
    });
    expect(second.id).toBe(first.id);
  });
});

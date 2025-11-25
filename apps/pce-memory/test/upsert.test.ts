import { describe, it, expect, beforeEach } from "vitest";
import { upsertClaim } from "../src/store/claims";
import { initDb, initSchema, resetDb } from "../src/db/connection";

beforeEach(async () => {
  resetDb();
  process.env.PCE_DB = ":memory:";
  await initDb();
  await initSchema();
});

describe("upsertClaim", () => {
  it("returns same id on duplicate content_hash", async () => {
    const { claim: first, isNew: isFirstNew } = await upsertClaim({
      text: "foo",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hash123",
    });
    expect(isFirstNew).toBe(true);

    const { claim: second, isNew: isSecondNew } = await upsertClaim({
      text: "foo2",
      kind: "fact",
      scope: "project",
      boundary_class: "internal",
      content_hash: "hash123",
    });
    expect(isSecondNew).toBe(false); // 重複なのでfalse
    expect(second.id).toBe(first.id);
  });
});

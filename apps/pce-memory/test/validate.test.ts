import { describe, it, expect, beforeEach } from "vitest";
import { boundaryValidate } from "@pce/boundary";
import { defaultPolicy } from "@pce/policy-schemas/src/defaults";

describe("boundary.validate", () => {
  it("returns error on unknown scope", () => {
    const res = boundaryValidate({ payload: "foo", allow: ["answer:task"], scope: "unknown" }, defaultPolicy.boundary);
    expect(res.allowed).toBe(false);
    expect(res.reason).toBe("SCOPE_UNKNOWN");
  });
});

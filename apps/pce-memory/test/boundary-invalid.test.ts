import { describe, it, expect } from "vitest";
import { boundaryValidate } from "@pce/boundary";
import { defaultPolicy } from "@pce/policy-schemas/src/defaults";

describe("boundary.validate error propagation", () => {
  it("returns SCOPE_UNKNOWN reason for unknown scope", () => {
    const res = boundaryValidate({ payload: "x", allow: ["answer:task"], scope: "unknown" }, defaultPolicy.boundary);
    expect(res.allowed).toBe(false);
    expect(res.reason).toBe("SCOPE_UNKNOWN");
  });
});

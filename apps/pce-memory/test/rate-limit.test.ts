import { describe, it, expect, beforeEach } from "vitest";
import { checkAndConsume, initRateState, resetRates } from "../src/store/rate";
import { initSchema } from "../src/db/connection";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  process.env.PCE_RATE_CAP = "1";
  initSchema();
  initRateState();
  resetRates();
});

describe("rate limit", () => {
  it("blocks when cap reached", () => {
    expect(checkAndConsume("tool")).toBe(true);
    expect(checkAndConsume("tool")).toBe(false);
  });
});

import { describe, it, expect, beforeEach } from "vitest";
import { checkAndConsume, initRateState, resetRates } from "../src/store/rate";
import { initSchema } from "../src/db/connection";

beforeEach(() => {
  process.env.PCE_DB = ":memory:";
  process.env.PCE_RATE_CAP = "1";
  process.env.PCE_RATE_WINDOW = "100"; // large window to avoid auto-reset
  initSchema();
  initRateState();
  resetRates();
});

describe("rate limit", () => {
  it("blocks when cap reached", () => {
    expect(checkAndConsume("tool")).toBe(true);
    expect(checkAndConsume("tool")).toBe(false);
  });

  it("resets after window elapsed", () => {
    const db = getDb().connect();
    expect(checkAndConsume("tool")).toBe(true);
    // simulate window expiry by setting last_reset back in time
    db.prepare("UPDATE rate_state SET last_reset = last_reset - 200 WHERE bucket = 'tool'").run();
    db.close();
    expect(checkAndConsume("tool")).toBe(true);
  });
});

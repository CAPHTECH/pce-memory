import { describe, it, expect, beforeEach } from "vitest";
import { checkAndConsume, initRateState, resetRates } from "../src/store/rate";
import { initDb, initSchema, resetDb, getConnection } from "../src/db/connection";

beforeEach(async () => {
  resetDb();
  process.env.PCE_DB = ":memory:";
  process.env.PCE_RATE_CAP = "1";
  process.env.PCE_RATE_WINDOW = "100"; // large window to avoid auto-reset
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe("rate limit", () => {
  it("blocks when cap reached", async () => {
    expect(await checkAndConsume("tool")).toBe(true);
    expect(await checkAndConsume("tool")).toBe(false);
  });

  it("resets after window elapsed", async () => {
    const conn = await getConnection();
    expect(await checkAndConsume("tool")).toBe(true);
    // simulate window expiry by setting last_reset back in time
    await conn.run("UPDATE rate_state SET last_reset = last_reset - 200 WHERE bucket = 'tool'");
    expect(await checkAndConsume("tool")).toBe(true);
  });
});

import { getConnection } from "../db/connection";

const DEFAULT_BUCKETS = ["tool", "policy", "activate"];

function cap(): number {
  const envCap = Number(process.env.PCE_RATE_CAP ?? "");
  return Number.isFinite(envCap) && envCap > 0 ? envCap : 100;
}

function windowSec(): number {
  const envWin = Number(process.env.PCE_RATE_WINDOW ?? "");
  return Number.isFinite(envWin) && envWin >= 0 ? envWin : 60; // seconds
}

export async function initRateState(): Promise<void> {
  const conn = await getConnection();
  for (const b of DEFAULT_BUCKETS) {
    await conn.run(
      "INSERT OR IGNORE INTO rate_state (bucket, value, last_reset) VALUES ($1, 0, epoch(now())::INTEGER)",
      [b]
    );
  }
}

async function getRow(bucket: string): Promise<{ value: number; last_reset: number } | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT value, last_reset FROM rate_state WHERE bucket = $1",
    [bucket]
  );
  const rows = reader.getRowObjects() as { value: number; last_reset: number }[];
  return rows[0];
}

export async function getRate(bucket: string): Promise<number> {
  const row = await getRow(bucket);
  return row?.value ?? 0;
}

export async function setRate(bucket: string, value: number): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    "INSERT INTO rate_state (bucket, value, last_reset) VALUES ($1, $2, epoch(now())::INTEGER) ON CONFLICT(bucket) DO UPDATE SET value=excluded.value, last_reset=excluded.last_reset",
    [bucket, value]
  );
}

/**
 * 単純な固定上限のカウンタ（時間窓付き）。上限を超えたら false を返す。
 * PCE_RATE_WINDOW (秒) を設定するとその時間でリセット。デフォルト60秒。
 */
export async function checkAndConsume(bucket: string): Promise<boolean> {
  const row = await getRow(bucket);
  const now = Math.floor(Date.now() / 1000);
  const win = windowSec();
  let current = row?.value ?? 0;
  const last = row?.last_reset ?? now;
  const resetNeeded = win > 0 && now - last >= win;
  if (resetNeeded) {
    current = 0;
    await setRate(bucket, 0); // also refresh last_reset
  }
  const limit = cap();
  if (current >= limit) return false;
  await setRate(bucket, current + 1);
  return true;
}

export async function resetRates(): Promise<void> {
  const conn = await getConnection();
  await conn.run("UPDATE rate_state SET value = 0");
}

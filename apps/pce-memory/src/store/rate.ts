import { getDb } from "../db/connection";

const DEFAULT_BUCKETS = ["tool", "policy", "activate"];

function cap(): number {
  const envCap = Number(process.env.PCE_RATE_CAP ?? "");
  return Number.isFinite(envCap) && envCap > 0 ? envCap : 100;
}

function windowSec(): number {
  const envWin = Number(process.env.PCE_RATE_WINDOW ?? "");
  return Number.isFinite(envWin) && envWin >= 0 ? envWin : 60; // seconds
}

export function initRateState() {
  const db = getDb().connect();
  try {
    DEFAULT_BUCKETS.forEach((b) => {
      db.prepare("INSERT OR IGNORE INTO rate_state (bucket, value, last_reset) VALUES (?, 0, strftime('%s','now'))").run(b);
    });
  } finally {
    db.close();
  }
}

function getRow(bucket: string): { value: number; last_reset: number } | undefined {
  const db = getDb().connect();
  try {
    const row = db.prepare("SELECT value, last_reset FROM rate_state WHERE bucket = ?").get(bucket) as
      | { value: number; last_reset: number }
      | undefined;
    return row;
  } finally {
    db.close();
  }
}

export function getRate(bucket: string): number {
  return getRow(bucket)?.value ?? 0;
}

export function setRate(bucket: string, value: number) {
  const db = getDb().connect();
  try {
    db.prepare(
      "INSERT INTO rate_state (bucket, value, last_reset) VALUES (?, ?, strftime('%s','now')) ON CONFLICT(bucket) DO UPDATE SET value=excluded.value, last_reset=excluded.last_reset"
    ).run(
      bucket,
      value
    );
  } finally {
    db.close();
  }
}

/**
 * 単純な固定上限のカウンタ（時間窓なし）。上限を超えたら false を返す。
 * PCE_RATE_WINDOW (秒) を設定するとその時間でリセット。デフォルト60秒。
 */
export function checkAndConsume(bucket: string): boolean {
  const row = getRow(bucket);
  const now = Math.floor(Date.now() / 1000);
  const win = windowSec();
  let current = row?.value ?? 0;
  const last = row?.last_reset ?? now;
  const resetNeeded = win > 0 && now - last >= win;
  if (resetNeeded) {
    current = 0;
    setRate(bucket, 0); // also refresh last_reset
  }
  const limit = cap();
  if (current >= limit) return false;
  setRate(bucket, current + 1);
  return true;
}

export function resetRates() {
  const db = getDb().connect();
  try {
    db.prepare("UPDATE rate_state SET value = 0").run();
  } finally {
    db.close();
  }
}

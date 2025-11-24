import { getDb } from "../db/connection";

const DEFAULT_BUCKETS = ["tool", "policy", "activate"];

function cap(): number {
  const envCap = Number(process.env.PCE_RATE_CAP ?? "");
  return Number.isFinite(envCap) && envCap > 0 ? envCap : 100;
}

export function initRateState() {
  const db = getDb().connect();
  try {
    DEFAULT_BUCKETS.forEach((b) => {
      db.prepare("INSERT OR IGNORE INTO rate_state (bucket, value) VALUES (?, 0)").run(b);
    });
  } finally {
    db.close();
  }
}

export function getRate(bucket: string): number {
  const db = getDb().connect();
  try {
    const row = db.prepare("SELECT value FROM rate_state WHERE bucket = ?").get(bucket) as { value: number } | undefined;
    return row?.value ?? 0;
  } finally {
    db.close();
  }
}

export function setRate(bucket: string, value: number) {
  const db = getDb().connect();
  try {
    db.prepare("INSERT INTO rate_state (bucket, value) VALUES (?, ?) ON CONFLICT(bucket) DO UPDATE SET value=excluded.value").run(
      bucket,
      value
    );
  } finally {
    db.close();
  }
}

/**
 * 単純な固定上限のカウンタ（時間窓なし）。上限を超えたら false を返す。
 * 実運用で時間窓を導入する場合は schema 拡張が必要。
 */
export function checkAndConsume(bucket: string): boolean {
  const current = getRate(bucket);
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

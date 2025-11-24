import { getDb } from "../db/connection";

const DEFAULT_BUCKETS = ["tool", "policy", "activate"];

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

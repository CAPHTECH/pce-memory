import { getConnection } from '../db/connection.js';

const DEFAULT_BUCKETS = ['tool', 'policy', 'activate'];

/**
 * レート制限の上限値を取得
 * デフォルト: 1000件/10秒（バルク登録に対応するため緩和）
 */
function cap(): number {
  const envCap = Number(process.env['PCE_RATE_CAP'] ?? '');
  return Number.isFinite(envCap) && envCap > 0 ? envCap : 1000;
}

/**
 * レート制限の時間窓（秒）を取得
 * デフォルト: 10秒（短い窓で頻繁にリセットし、一時的な制限からの回復を早める）
 */
function windowSec(): number {
  const envWin = Number(process.env['PCE_RATE_WINDOW'] ?? '');
  return Number.isFinite(envWin) && envWin >= 0 ? envWin : 10; // seconds
}

/**
 * rate_stateテーブルを初期化する。
 * デーモン起動時に呼び出され、すべてのバケットのカウンタをリセットする。
 *
 * Note: INSERT OR IGNOREではなくON CONFLICT DO UPDATEを使用することで、
 * デーモン再起動時にrate limitが正しくリセットされるようにする。
 * これにより、永続化DBを使用している場合でも、デーモン起動時にクリーンな状態から開始できる。
 */
export async function initRateState(): Promise<void> {
  const conn = await getConnection();
  for (const b of DEFAULT_BUCKETS) {
    await conn.run(
      `INSERT INTO rate_state (bucket, value, last_reset)
       VALUES ($1, 0, epoch(now())::INTEGER)
       ON CONFLICT(bucket) DO UPDATE SET value = 0, last_reset = epoch(now())::INTEGER`,
      [b]
    );
  }
}

async function getRow(bucket: string): Promise<{ value: number; last_reset: number } | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT value, last_reset FROM rate_state WHERE bucket = $1',
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
    'INSERT INTO rate_state (bucket, value, last_reset) VALUES ($1, $2, epoch(now())::INTEGER) ON CONFLICT(bucket) DO UPDATE SET value=excluded.value, last_reset=excluded.last_reset',
    [bucket, value]
  );
}

/**
 * 単純な固定上限のカウンタ（時間窓付き）。上限を超えたら false を返す。
 * PCE_RATE_WINDOW (秒) を設定するとその時間でリセット。デフォルト60秒。
 * アトミックな UPDATE ... WHERE ... RETURNING で競合状態を回避。
 */
export async function checkAndConsume(bucket: string): Promise<boolean> {
  const conn = await getConnection();
  const now = Math.floor(Date.now() / 1000);
  const win = windowSec();
  const limit = cap();

  // まず時間窓リセットが必要かチェック（アトミックにリセット）
  if (win > 0) {
    await conn.run(
      'UPDATE rate_state SET value = 0, last_reset = $1 WHERE bucket = $2 AND ($1 - last_reset) >= $3',
      [now, bucket, win]
    );
  }

  // アトミックに条件付きインクリメント: value < limit の場合のみ更新
  const reader = await conn.runAndReadAll(
    'UPDATE rate_state SET value = value + 1 WHERE bucket = $1 AND value < $2 RETURNING value',
    [bucket, limit]
  );
  const rows = reader.getRowObjects() as { value: number }[];

  // 更新された行があれば成功、なければレート制限超過
  return rows.length > 0;
}

export async function resetRates(): Promise<void> {
  const conn = await getConnection();
  await conn.run('UPDATE rate_state SET value = 0');
}

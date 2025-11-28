/**
 * シリアライゼーションユーティリティ
 * DuckDBのBigIntタイムスタンプをJSON互換形式に変換
 *
 * 背景:
 * DuckDB Node API (@duckdb/node-api) はTIMESTAMP列をBigInt（マイクロ秒単位）で返す。
 * v1.4.x では {micros: bigint} オブジェクト形式で返される場合がある。
 * JSON.stringifyはBigIntをシリアライズできないため、ISO 8601文字列に変換する必要がある。
 */

/**
 * DuckDBタイムスタンプ値の型
 * @duckdb/node-api 1.4.x では {micros: bigint} オブジェクトとして返される
 */
interface DuckDBTimestamp {
  micros: bigint;
}

/**
 * DuckDBタイムスタンプオブジェクトかどうかを判定
 */
function isDuckDBTimestamp(value: unknown): value is DuckDBTimestamp {
  return (
    typeof value === 'object' &&
    value !== null &&
    'micros' in value &&
    typeof (value as DuckDBTimestamp).micros === 'bigint'
  );
}

/**
 * 変換済みDuckDBタイムスタンプオブジェクト（{micros: string}形式）かどうかを判定
 * JSON.stringifyのreplacerは深さ優先で処理するため、
 * 内部のbigintが先にstringに変換された後にオブジェクト自体が処理される
 */
interface ConvertedDuckDBTimestamp {
  micros: string;
}

function isConvertedDuckDBTimestamp(value: unknown): value is ConvertedDuckDBTimestamp {
  return (
    typeof value === 'object' &&
    value !== null &&
    'micros' in value &&
    typeof (value as ConvertedDuckDBTimestamp).micros === 'string' &&
    Object.keys(value as object).length === 1
  );
}

/**
 * DuckDB BigIntタイムスタンプをISO 8601文字列に変換
 * DuckDBはTIMESTAMP列をマイクロ秒単位のBigIntまたは{micros: bigint}オブジェクトで返す
 *
 * @param value - 変換対象の値
 * @returns BigIntまたはDuckDBTimestampの場合はISO 8601文字列、Dateの場合もISO 8601文字列、それ以外はそのまま
 */
export function normalizeTimestamp(value: unknown): string | unknown {
  // DuckDB node-api 1.4.x: {micros: bigint} オブジェクト形式
  if (isDuckDBTimestamp(value)) {
    return new Date(Number(value.micros / 1000n)).toISOString();
  }
  // 旧形式: BigInt直接
  if (typeof value === 'bigint') {
    // DuckDBはマイクロ秒単位で返すため、ミリ秒に変換
    return new Date(Number(value / 1000n)).toISOString();
  }
  if (value instanceof Date) {
    return value.toISOString();
  }
  return value;
}

/**
 * タイムスタンプフィールドのデフォルトリスト
 */
const DEFAULT_TIMESTAMP_FIELDS = [
  'created_at',
  'updated_at',
  'recency_anchor',
  'at',
  'ts',
  'ts_eff',
  'recorded_at',
  'last_reset',
];

/**
 * データベース行のタイムスタンプフィールドを正規化
 *
 * @param row - データベースから取得した行オブジェクト
 * @param timestampFields - 正規化対象のフィールド名リスト
 * @returns タイムスタンプが正規化された行オブジェクト
 */
export function normalizeRowTimestamps<T>(
  row: T,
  timestampFields: string[] = DEFAULT_TIMESTAMP_FIELDS
): T {
  if (row === null || row === undefined || typeof row !== 'object') {
    return row;
  }
  const normalized = { ...row } as Record<string, unknown>;
  for (const field of timestampFields) {
    if (field in normalized) {
      normalized[field] = normalizeTimestamp(normalized[field]);
    }
  }
  return normalized as T;
}

/**
 * 配列の各要素のタイムスタンプを正規化
 *
 * @param rows - データベースから取得した行オブジェクトの配列
 * @param timestampFields - 正規化対象のフィールド名リスト
 * @returns タイムスタンプが正規化された行オブジェクトの配列
 */
export function normalizeRowsTimestamps<T>(
  rows: T[],
  timestampFields: string[] = DEFAULT_TIMESTAMP_FIELDS
): T[] {
  return rows.map((row) => normalizeRowTimestamps(row, timestampFields));
}

/**
 * BigIntを安全にJSON変換するreplacer関数
 * JSON.stringifyの第2引数として使用
 *
 * BigIntは以下のように変換:
 * - タイムスタンプと思われる値（マイクロ秒、2000-2100年の範囲）: ISO 8601文字列
 * - Number.MAX_SAFE_INTEGER以下: number型
 * - それ以上: 文字列
 *
 * DuckDBTimestamp ({micros: bigint}) オブジェクトも処理
 *
 * @param _key - オブジェクトのキー（使用しない）
 * @param value - 変換対象の値
 * @returns JSON互換の値
 */
export function bigIntReplacer(_key: string, value: unknown): unknown {
  // DuckDB node-api 1.4.x: {micros: bigint} オブジェクト形式
  if (isDuckDBTimestamp(value)) {
    return new Date(Number(value.micros / 1000n)).toISOString();
  }

  // JSON.stringifyの深さ優先処理により、内部のbigintが先に変換された {micros: string} 形式
  if (isConvertedDuckDBTimestamp(value)) {
    return value.micros;
  }

  if (typeof value === 'bigint') {
    // DuckDBのタイムスタンプはマイクロ秒単位
    // 妥当な日付範囲（2000-01-01 〜 2100-01-01）のマイクロ秒値
    // 2000-01-01: 946684800000000 (約9.5e14)
    // 2100-01-01: 4102444800000000 (約4.1e15)
    // この範囲はNumber.MAX_SAFE_INTEGER (約9e15) より小さいため安全
    const MIN_TIMESTAMP_US = 946_684_800_000_000n; // 2000-01-01
    const MAX_TIMESTAMP_US = 4_102_444_800_000_000n; // 2100-01-01

    // タイムスタンプとして妥当な範囲かチェック
    if (value >= MIN_TIMESTAMP_US && value <= MAX_TIMESTAMP_US) {
      return new Date(Number(value / 1000n)).toISOString();
    }

    // Number.MAX_SAFE_INTEGER以下の通常の数値
    if (value <= BigInt(Number.MAX_SAFE_INTEGER) && value >= BigInt(-Number.MAX_SAFE_INTEGER)) {
      return Number(value);
    }

    // 大きな数値は文字列として保持
    return value.toString();
  }
  return value;
}

/**
 * BigIntを含むオブジェクトを安全にJSON文字列化
 *
 * @param value - シリアライズ対象のオブジェクト
 * @returns JSON文字列
 */
export function safeJsonStringify(value: unknown): string {
  return JSON.stringify(value, bigIntReplacer);
}

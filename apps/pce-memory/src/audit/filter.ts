/**
 * 機密データフィルタリング
 * ログに機密情報を残さないためのユーティリティ
 */
import { createHash } from "crypto";

// フィルタ対象のフィールド名パターン
const SENSITIVE_FIELDS = [
  "email",
  "phone",
  "password",
  "secret",
  "token",
  "authorization",
  "api_key",
  "apikey",
  "credential",
  "private_key",
  "privatekey",
] as const;

// フィールド名が機密かどうかを判定（大文字小文字無視）
function isSensitiveField(fieldName: string): boolean {
  const lower = fieldName.toLowerCase();
  return SENSITIVE_FIELDS.some((sensitive) => lower.includes(sensitive));
}

/**
 * オブジェクトから機密フィールドをマスク
 * 再帰的に処理し、機密フィールドは "[REDACTED]" に置換
 */
export function redactSensitiveFields<T>(obj: T): T {
  if (obj === null || obj === undefined) {
    return obj;
  }

  if (typeof obj !== "object") {
    return obj;
  }

  if (Array.isArray(obj)) {
    return obj.map((item) => redactSensitiveFields(item)) as T;
  }

  const result: Record<string, unknown> = {};
  for (const [key, value] of Object.entries(obj)) {
    if (isSensitiveField(key)) {
      result[key] = "[REDACTED]";
    } else if (typeof value === "object" && value !== null) {
      result[key] = redactSensitiveFields(value);
    } else {
      result[key] = value;
    }
  }
  return result as T;
}

/**
 * 文字列のSHA256ダイジェストを生成
 * ペイロード内容をログに残さず、検証用ハッシュのみ記録
 */
export function computeDigest(content: string): string {
  return `sha256:${createHash("sha256").update(content, "utf8").digest("hex")}`;
}

/**
 * 監査ログ用にペイロードを安全化
 * 内容をダイジェストに置換し、機密フィールドをマスク
 */
export interface SafePayload {
  payload_digest: string;
  payload_length: number;
  metadata?: Record<string, unknown>;
}

export function sanitizeForAudit(
  payload: string,
  metadata?: Record<string, unknown>
): SafePayload {
  return {
    payload_digest: computeDigest(payload),
    payload_length: payload.length,
    metadata: metadata ? redactSensitiveFields(metadata) : undefined,
  };
}

/**
 * エラーメッセージから機密情報を除去
 * スタックトレースやパス情報を含まない安全なメッセージを返す
 */
export function sanitizeErrorMessage(error: unknown): string {
  if (error instanceof Error) {
    // スタックトレースは除外、メッセージのみ
    const msg = error.message;
    // パス情報を除去
    return msg.replace(/\/[^\s]+/g, "[PATH]");
  }
  return String(error);
}

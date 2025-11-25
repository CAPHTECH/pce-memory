/**
 * 環境変数の読み込みとバリデーション
 * PCE Memory MCP Server の設定を管理
 */
import { z } from "zod";

// 環境変数スキーマ定義
const envSchema = z.object({
  // DuckDB パス（デフォルト: インメモリ）
  PCE_DB: z.string().default(":memory:"),

  // 認証トークン（本番環境では必須）
  PCE_TOKEN: z.string().optional(),

  // デフォルトポリシーファイルパス
  PCE_POLICY: z.string().optional(),

  // 監査ログ出力先（ファイルパス）
  AUDIT_LOG_PATH: z.string().optional(),

  // 実行環境
  NODE_ENV: z.enum(["development", "production", "test"]).default("development"),
});

export type Env = z.infer<typeof envSchema>;

let cachedEnv: Env | null = null;

/**
 * 環境変数を読み込み、バリデーションを実行
 * 本番環境では PCE_TOKEN が必須
 */
export function loadEnv(): Env {
  if (cachedEnv) return cachedEnv;

  const result = envSchema.safeParse(process.env);

  if (!result.success) {
    const errors = result.error.errors.map((e) => `${e.path.join(".")}: ${e.message}`).join(", ");
    throw new Error(`ENV_VALIDATION_FAILED: ${errors}`);
  }

  const env = result.data;

  // 本番環境では PCE_TOKEN 必須
  if (env.NODE_ENV === "production" && !env.PCE_TOKEN) {
    throw new Error("ENV_VALIDATION_FAILED: PCE_TOKEN is required in production");
  }

  cachedEnv = env;
  return env;
}

/**
 * 認証トークンの検証
 * 開発環境ではトークンなしでも許可
 */
export function validateToken(token: string | undefined, env: Env): boolean {
  // 開発/テスト環境ではトークンなしを許可
  if (env.NODE_ENV !== "production" && !env.PCE_TOKEN) {
    return true;
  }

  // トークンが設定されている場合は一致を確認
  if (env.PCE_TOKEN) {
    return token === env.PCE_TOKEN;
  }

  return false;
}

/**
 * テスト用: キャッシュをクリア
 */
export function clearEnvCache(): void {
  cachedEnv = null;
}

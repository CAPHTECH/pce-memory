import { getConnection } from "../db/connection.js";
import { appendFileSync, existsSync, mkdirSync } from "fs";
import { dirname } from "path";

export interface AuditLog {
  id: string;
  op: string;
  ok: boolean;
  req?: string;
  trace?: string;
  policy_version?: string;
}

/**
 * 監査ログファイル用の拡張レコード（JSONL形式）
 */
export interface AuditFileRecord {
  ts: string; // ISO 8601 timestamp
  request_id: string;
  trace_id: string;
  policy_version: string;
  op: string;
  ok: boolean;
  subject?: string;
  payload_digest?: string;
}

// 監査ログファイルパス（環境変数から取得）
let auditLogPath: string | null = null;

/**
 * 監査ログファイルパスを設定
 */
export function setAuditLogPath(path: string | undefined): void {
  auditLogPath = path ?? null;
}

/**
 * DuckDBへの監査ログ追記（非同期）
 */
export async function appendLog(entry: AuditLog): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    "INSERT INTO logs (id, op, ok, req, trace, policy_version) VALUES ($1, $2, $3, $4, $5, $6)",
    [
      entry.id,
      entry.op,
      entry.ok,
      entry.req ?? null,
      entry.trace ?? null,
      entry.policy_version ?? null
    ]
  );
}

/**
 * 監査ログファイルへの追記（append-only JSONL形式）
 * AUDIT_LOG_PATH が設定されている場合のみ出力
 */
export function appendAuditFile(record: Omit<AuditFileRecord, "ts">): void {
  if (!auditLogPath) return;

  // ディレクトリが存在しない場合は作成
  const dir = dirname(auditLogPath);
  if (!existsSync(dir)) {
    mkdirSync(dir, { recursive: true });
  }

  const fullRecord: AuditFileRecord = {
    ts: new Date().toISOString(),
    ...record,
  };

  // JSONL形式で追記（1行1JSON + 改行）
  const line = JSON.stringify(fullRecord) + "\n";
  appendFileSync(auditLogPath, line, { encoding: "utf-8" });
}

/**
 * 統合ログ出力（DuckDB + ファイル両方に記録）
 */
export async function recordAudit(
  entry: AuditLog,
  extra?: { subject?: string; payload_digest?: string }
): Promise<void> {
  // DuckDBに記録
  await appendLog(entry);

  // ファイルにも記録（パスが設定されている場合）
  const record: Omit<AuditFileRecord, "ts"> = {
    request_id: entry.req ?? entry.id,
    trace_id: entry.trace ?? "",
    policy_version: entry.policy_version ?? "",
    op: entry.op,
    ok: entry.ok,
  };
  if (extra?.subject) {
    record.subject = extra.subject;
  }
  if (extra?.payload_digest) {
    record.payload_digest = extra.payload_digest;
  }
  appendAuditFile(record);
}

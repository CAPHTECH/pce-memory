import { getDb } from "../db/connection";

export interface AuditLog {
  id: string;
  op: string;
  ok: boolean;
  req?: string;
  trace?: string;
  policy_version?: string;
}

export function appendLog(entry: AuditLog) {
  const db = getDb().connect();
  try {
    db.prepare("INSERT INTO logs (id, op, ok, req, trace, policy_version) VALUES (?,?,?,?,?,?)").run(
      entry.id,
      entry.op,
      entry.ok,
      entry.req ?? null,
      entry.trace ?? null,
      entry.policy_version ?? null
    );
  } finally {
    db.close();
  }
}

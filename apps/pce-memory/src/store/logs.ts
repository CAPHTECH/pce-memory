import { getDb } from "../db/connection";

export interface AuditLog {
  id: string;
  op: string;
  ok: boolean;
  req?: string;
}

export function appendLog(entry: AuditLog) {
  const db = getDb().connect();
  try {
    db.prepare("INSERT INTO logs (id, op, ok, req) VALUES (?,?,?,?)").run(
      entry.id,
      entry.op,
      entry.ok,
      entry.req ?? null
    );
  } finally {
    db.close();
  }
}

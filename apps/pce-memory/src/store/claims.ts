import { getDb } from "../db/connection";

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
}

export function upsertClaim(c: Omit<Claim, "id">): Claim {
  const db = getDb().connect();
  try {
    const existing = db.prepare("SELECT id,text,kind,scope,boundary_class,content_hash FROM claims WHERE content_hash = ?").get(c.content_hash) as Claim | undefined;
    if (existing) return existing;
    const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
    db.prepare(
      "INSERT INTO claims (id,text,kind,scope,boundary_class,content_hash) VALUES (?,?,?,?,?,?)"
    ).run(id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash);
    return { id, ...c };
  } catch (e: any) {
    // UNIQUE 制約違反などは既存レコードを返す（idempotent upsert）
    const existing = db.prepare("SELECT id,text,kind,scope,boundary_class,content_hash FROM claims WHERE content_hash = ?").get(c.content_hash) as Claim | undefined;
    if (existing) return existing;
    throw e;
  } finally {
    db.close();
  }
}

export function listClaimsByScope(scopes: string[], limit: number): Claim[] {
  const db = getDb().connect();
  try {
    const inClause = scopes.map(() => "?").join(",");
    const stmt = db.prepare(
      `SELECT id,text,kind,scope,boundary_class,content_hash FROM claims WHERE scope IN (${inClause}) LIMIT ?`
    );
    const rows = stmt.all(...scopes, limit) as Claim[];
    return rows;
  } finally {
    db.close();
  }
}

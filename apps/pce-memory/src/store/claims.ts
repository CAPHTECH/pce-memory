import { getConnection } from "../db/connection";

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
}

export async function upsertClaim(c: Omit<Claim, "id">): Promise<Claim> {
  const conn = await getConnection();
  try {
    // 既存レコードをチェック
    const reader = await conn.runAndReadAll(
      "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE content_hash = $1",
      [c.content_hash]
    );
    const existing = reader.getRowObjects() as Claim[];
    if (existing.length > 0) return existing[0];

    // 新規レコード挿入
    const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
    await conn.run(
      "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ($1, $2, $3, $4, $5, $6)",
      [id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash]
    );
    return { id, ...c };
  } catch (e: any) {
    // UNIQUE 制約違反などは既存レコードを返す（idempotent upsert）
    const reader = await conn.runAndReadAll(
      "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE content_hash = $1",
      [c.content_hash]
    );
    const existing = reader.getRowObjects() as Claim[];
    if (existing.length > 0) return existing[0];
    throw e;
  }
}

export async function listClaimsByScope(scopes: string[], limit: number, q?: string): Promise<Claim[]> {
  const conn = await getConnection();
  const hasQuery = q && q.trim().length > 0;

  // DuckDBはプレースホルダーのIN句に配列をそのまま渡せないため、動的にSQL構築
  const placeholders = scopes.map((_, i) => `$${i + 1}`).join(",");
  const sql = hasQuery
    ? `SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash, coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders}) AND c.text LIKE $${scopes.length + 1}
       ORDER BY score DESC
       LIMIT $${scopes.length + 2}`
    : `SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash, coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders})
       ORDER BY score DESC
       LIMIT $${scopes.length + 1}`;

  const args = hasQuery ? [...scopes, `%${q}%`, limit] : [...scopes, limit];
  const reader = await conn.runAndReadAll(sql, args);
  return reader.getRowObjects() as Claim[];
}

export async function findClaimById(id: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE id = $1",
    [id]
  );
  const rows = reader.getRowObjects() as Claim[];
  return rows[0];
}

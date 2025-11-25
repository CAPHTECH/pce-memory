import { getConnection } from "../db/connection.js";

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
}

/**
 * upsertClaimの戻り値型
 * isNew: 新規挿入された場合はtrue、既存レコードを返した場合はfalse
 */
export interface UpsertResult {
  claim: Claim;
  isNew: boolean;
}

/**
 * Claimを登録（idempotent upsert）
 * 既存のcontent_hashがある場合は既存レコードを返す（isNew: false）
 * 新規の場合は挿入して返す（isNew: true）
 */
export async function upsertClaim(c: Omit<Claim, "id">): Promise<UpsertResult> {
  const conn = await getConnection();
  try {
    // 既存レコードをチェック
    const reader = await conn.runAndReadAll(
      "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE content_hash = $1",
      [c.content_hash]
    );
    const existing = reader.getRowObjects() as unknown as Claim[];
    if (existing.length > 0 && existing[0]) {
      return { claim: existing[0], isNew: false };
    }

    // 新規レコード挿入
    const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
    await conn.run(
      "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ($1, $2, $3, $4, $5, $6)",
      [id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash]
    );
    return { claim: { id, ...c }, isNew: true };
  } catch (e: unknown) {
    // UNIQUE 制約違反などは既存レコードを返す（idempotent upsert）
    const reader = await conn.runAndReadAll(
      "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE content_hash = $1",
      [c.content_hash]
    );
    const existing = reader.getRowObjects() as unknown as Claim[];
    if (existing.length > 0 && existing[0]) {
      return { claim: existing[0], isNew: false };
    }
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
  return reader.getRowObjects() as unknown as Claim[];
}

export async function findClaimById(id: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE id = $1",
    [id]
  );
  const rows = reader.getRowObjects() as unknown as Claim[];
  return rows[0];
}

/**
 * DBに登録されているClaimの総数を取得
 * サーバー再起動時の状態復元に使用
 */
export async function countClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll("SELECT COUNT(*) as cnt FROM claims");
  const rows = reader.getRowObjects() as unknown as { cnt: number | bigint }[];
  return rows[0] ? Number(rows[0].cnt) : 0;
}

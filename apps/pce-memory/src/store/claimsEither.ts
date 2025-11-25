/**
 * Claims Store（Either版）
 * V1 Conservative設計: Either<DomainError, T>を返す
 * TLA+ Upsertに対応
 */
import * as TE from "fp-ts/TaskEither";
import { pipe } from "fp-ts/function";
import { getConnection } from "../db/connection.js";
import type { DomainError } from "../domain/errors.js";
import { dbError } from "../domain/errors.js";

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
}

/**
 * Claim取得（Either版）
 */
export const findClaimByIdE = (
  id: string
): TE.TaskEither<DomainError, Claim | undefined> => {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE id = $1",
        [id]
      );
      const rows = reader.getRowObjects() as unknown as Claim[];
      return rows[0];
    },
    (e) => dbError(e)
  );
};

/**
 * content_hashでClaim取得
 */
export const findClaimByHashE = (
  contentHash: string
): TE.TaskEither<DomainError, Claim | undefined> => {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        "SELECT id, text, kind, scope, boundary_class, content_hash FROM claims WHERE content_hash = $1",
        [contentHash]
      );
      const rows = reader.getRowObjects() as unknown as Claim[];
      return rows[0];
    },
    (e) => dbError(e)
  );
};

/**
 * Claim Upsert（Either版）
 * TLA+ V1_Upsertに対応:
 * - 成功ケース（Right）: 新規または空のallow
 * - 失敗ケース（Left）: 重複（既存claimのallowが非空）
 *
 * 注: 現在の実装では重複チェックはcontent_hashベース
 */
export const upsertClaimE = (
  c: Omit<Claim, "id">
): TE.TaskEither<DomainError, Claim> => {
  return pipe(
    findClaimByHashE(c.content_hash),
    TE.chain((existing) => {
      if (existing) {
        // 既存レコードがある場合は成功（idempotent）
        return TE.right(existing);
      }

      // 新規レコード挿入
      return TE.tryCatch(
        async () => {
          const conn = await getConnection();
          const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
          await conn.run(
            "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ($1, $2, $3, $4, $5, $6)",
            [id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash]
          );
          return { id, ...c };
        },
        (e) => dbError(e)
      );
    })
  );
};

/**
 * スコープ別Claim一覧取得（Either版）
 */
export const listClaimsByScopeE = (
  scopes: string[],
  limit: number,
  q?: string
): TE.TaskEither<DomainError, Claim[]> => {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();
      const hasQuery = q && q.trim().length > 0;

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
    },
    (e) => dbError(e)
  );
};

/**
 * Claim存在確認（Either版）
 */
export const claimExistsE = (
  id: string
): TE.TaskEither<DomainError, boolean> => {
  return pipe(
    findClaimByIdE(id),
    TE.map((claim) => claim !== undefined)
  );
};

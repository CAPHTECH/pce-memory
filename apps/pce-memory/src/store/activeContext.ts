import { getConnection } from "../db/connection.js";
import type { Claim } from "./claims.js";
import { safeJsonStringify } from "../utils/serialization.js";

export interface ActiveContext {
  id: string;
  claims: Claim[];
}

export async function saveActiveContext(ac: ActiveContext): Promise<void> {
  const conn = await getConnection();
  // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
  await conn.run(
    "INSERT INTO active_contexts (id, claims) VALUES ($1, $2)",
    [ac.id, safeJsonStringify(ac.claims)]
  );
}

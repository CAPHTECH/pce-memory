import { getConnection } from "../db/connection.js";
import type { Claim } from "./claims.js";

export interface ActiveContext {
  id: string;
  claims: Claim[];
}

export async function saveActiveContext(ac: ActiveContext): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    "INSERT INTO active_contexts (id, claims) VALUES ($1, $2)",
    [ac.id, JSON.stringify(ac.claims)]
  );
}

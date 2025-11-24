import { getDb } from "../db/connection";
import { Claim } from "./claims";

export interface ActiveContext {
  id: string;
  claims: Claim[];
}

export function saveActiveContext(ac: ActiveContext) {
  const db = getDb().connect();
  try {
    db.prepare("INSERT INTO active_contexts (id, claims) VALUES (?, ?)").run(ac.id, JSON.stringify(ac.claims));
  } finally {
    db.close();
  }
}

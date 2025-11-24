#!/usr/bin/env node

/**
 * 簡易インメモリ実装の MCP ツール群。
 * 本番では DuckDB・正式な MCP transport に置き換えること。
 */
import { parsePolicy, defaultPolicy } from "@pce/policy-schemas";
import { boundaryValidate } from "@pce/boundary";

type Scope = "session" | "project" | "principle";

interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: Scope;
  boundary_class: string;
  content_hash: string;
}

interface ActiveContext {
  id: string;
  claims: Claim[];
}

const claimsStore: Map<string, Claim> = new Map();
const acStore: Map<string, ActiveContext> = new Map();

// util
function newId(prefix: string) {
  return `${prefix}_${Math.random().toString(36).slice(2, 8)}`;
}

export function policyApply(yaml?: string) {
  const doc = yaml ? parsePolicy(yaml) : { ok: true, value: defaultPolicy };
  if (!doc.ok) throw new Error(doc.errors?.join(",") ?? "policy apply failed");
  currentPolicy = doc.value!.boundary;
  return { policy_version: doc.value!.version };
}

let currentPolicy = defaultPolicy.boundary;

export function upsert(input: Omit<Claim, "id">) {
  if (!input.content_hash) throw new Error("content_hash required");
  if (claimsStore.has(input.content_hash)) return { id: claimsStore.get(input.content_hash)!.id };
  const id = newId("clm");
  const claim: Claim = { id, ...input };
  claimsStore.set(input.content_hash, claim);
  return { id };
}

export function activate(params: { q: string; scope: Scope[]; allow: string[]; top_k?: number }) {
  const acId = newId("ac");
  const matched = Array.from(claimsStore.values()).filter((c) => params.scope.includes(c.scope));
  const limited = matched.slice(0, params.top_k ?? 12);
  const ac: ActiveContext = { id: acId, claims: limited };
  acStore.set(acId, ac);
  return { active_context_id: acId, claims: limited };
}

export function boundaryValidateTool(payload: string, allow: string[], scope: Scope) {
  return boundaryValidate({ payload, allow, scope }, currentPolicy);
}

export function feedback(input: { claim_id: string; signal: "helpful" | "harmful" | "outdated"; score?: number }) {
  // 簡易実装: 何も更新しないが成功を返す
  if (!claimsStore.size) throw new Error("no claims");
  return { ok: true };
}

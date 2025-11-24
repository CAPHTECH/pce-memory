/**
 * PCE Memory MCP Server (stdio)
 * 本番用の最小実装: DuckDB ストア + ポリシー適用 + 境界チェック + upsert/activate/feedback
 */
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import { parsePolicy, defaultPolicy, BoundaryPolicy } from "@pce/policy-schemas";
import { boundaryValidate } from "@pce/boundary";
import { initSchema } from "./db/connection";
import { upsertClaim, listClaimsByScope, Claim } from "./store/claims";
import { saveActiveContext } from "./store/activeContext";
import { recordFeedback } from "./store/feedback";

type Scope = "session" | "project" | "principle";

let currentPolicy: BoundaryPolicy = defaultPolicy.boundary;

function applyPolicy(yaml?: string) {
  const doc = yaml ? parsePolicy(yaml) : { ok: true, value: defaultPolicy };
  if (!doc.ok || !doc.value) throw new Error(doc.errors?.join(",") ?? "policy apply failed");
  currentPolicy = doc.value.boundary;
  return { policy_version: doc.value.version };
}

async function registerTools(server: Server) {
  server.setRequestHandler("pce.memory.policy.apply", async (req) => {
    const yaml = req.params?.yaml as string | undefined;
    return applyPolicy(yaml);
  });

  server.setRequestHandler("pce.memory.upsert", async (req) => {
    const { text, kind, scope, boundary_class, content_hash } = req.params as any;
    if (!text || !kind || !scope || !boundary_class || !content_hash) throw new Error("missing fields");
    const claim = upsertClaim({ text, kind, scope, boundary_class, content_hash });
    return { id: claim.id };
  });

  server.setRequestHandler("pce.memory.activate", async (req) => {
    const { scope, allow, top_k } = req.params as any;
    if (!Array.isArray(scope) || !Array.isArray(allow)) throw new Error("scope/allow must be arrays");
    const claims: Claim[] = listClaimsByScope(scope, top_k ?? 12);
    const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
    saveActiveContext({ id: acId, claims });
    return { active_context_id: acId, claims };
  });

  server.setRequestHandler("pce.memory.boundary.validate", async (req) => {
    const { payload, allow, scope } = req.params as any;
    return boundaryValidate({ payload, allow, scope }, currentPolicy);
  });

  server.setRequestHandler("pce.memory.feedback", async (req) => {
    const { claim_id, signal, score } = req.params as any;
    if (!claim_id || !signal) throw new Error("claim_id/signal required");
    return recordFeedback({ claim_id, signal, score });
  });
}

async function main() {
  initSchema();
  const server = new Server({});
  await registerTools(server);
  const transport = new StdioServerTransport();
  await server.connect(transport);
}

main().catch((err) => {
  console.error("Fatal error:", err);
  process.exit(1);
});

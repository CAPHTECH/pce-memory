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
import { appendLog } from "./store/logs";

type Scope = "session" | "project" | "principle";

let currentPolicy: BoundaryPolicy = defaultPolicy.boundary;
let currentPolicyVersion = defaultPolicy.version ?? "0.1";

type ErrorCode =
  | "POLICY_INVALID"
  | "UPSERT_FAILED"
  | "ACTIVATE_FAILED"
  | "BOUNDARY_ERROR"
  | "FEEDBACK_FAILED"
  | "VALIDATION_ERROR";

function err(code: ErrorCode, message: string, request_id: string) {
  return { error: { code, message }, request_id };
}

function applyPolicy(yaml?: string) {
  const doc = yaml ? parsePolicy(yaml) : { ok: true, value: defaultPolicy };
  if (!doc.ok || !doc.value) throw new Error(doc.errors?.join(",") ?? "policy apply failed");
  currentPolicy = doc.value.boundary;
  currentPolicyVersion = doc.value.version;
  return { policy_version: doc.value.version };
}

async function registerTools(server: Server) {
  server.setRequestHandler("pce.memory.policy.apply", async (req) => {
    const yaml = req.params?.yaml as string | undefined;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      const res = applyPolicy(yaml);
      appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("POLICY_INVALID", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.upsert", async (req) => {
    const { text, kind, scope, boundary_class, content_hash } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!text || !kind || !scope || !boundary_class || !content_hash) {
        return { ...err("VALIDATION_ERROR", "missing fields", reqId), trace_id: traceId };
      }
      const claim = upsertClaim({ text, kind, scope, boundary_class, content_hash });
      appendLog({ id: `log_${reqId}`, op: "upsert", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { id: claim.id, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      appendLog({ id: `log_${reqId}`, op: "upsert", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("UPSERT_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.activate", async (req) => {
    const { scope, allow, top_k } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!Array.isArray(scope) || !Array.isArray(allow)) return { ...err("VALIDATION_ERROR", "scope/allow must be arrays", reqId), trace_id: traceId };
      const invalidScope = scope.some((s: string) => !["session", "project", "principle"].includes(s));
      if (invalidScope) return { ...err("VALIDATION_ERROR", "unknown scope", reqId), trace_id: traceId };
      if (allow.some((a: any) => typeof a !== "string")) return { ...err("VALIDATION_ERROR", "allow must be string[]", reqId), trace_id: traceId };
      const claims: Claim[] = listClaimsByScope(scope, top_k ?? 12);
      const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
      saveActiveContext({ id: acId, claims });
      appendLog({ id: `log_${reqId}`, op: "activate", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { active_context_id: acId, claims, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      appendLog({ id: `log_${reqId}`, op: "activate", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("ACTIVATE_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.boundary.validate", async (req) => {
    const { payload, allow, scope } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      const res = boundaryValidate({ payload, allow, scope }, currentPolicy);
      appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: res.allowed, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("BOUNDARY_ERROR", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.feedback", async (req) => {
    const { claim_id, signal, score } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!claim_id || !signal) return { ...err("VALIDATION_ERROR", "claim_id/signal required", reqId), trace_id: traceId };
      const res = recordFeedback({ claim_id, signal, score });
      appendLog({ id: `log_${reqId}`, op: "feedback", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      appendLog({ id: `log_${reqId}`, op: "feedback", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("FEEDBACK_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
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

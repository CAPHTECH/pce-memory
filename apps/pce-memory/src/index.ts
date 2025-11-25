/**
 * PCE Memory MCP Server (stdio)
 * 本番用の最小実装: DuckDB ストア + ポリシー適用 + 境界チェック + upsert/activate/feedback
 */
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  ListToolsRequestSchema,
  CallToolRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { parsePolicy, defaultPolicy, BoundaryPolicy } from "@pce/policy-schemas";
import { boundaryValidate } from "@pce/boundary";
import { initDb, initSchema } from "./db/connection";
import { upsertClaim, listClaimsByScope, Claim, findClaimById } from "./store/claims";
import { saveActiveContext } from "./store/activeContext";
import { recordFeedback } from "./store/feedback";
import { appendLog, setAuditLogPath } from "./store/logs";
import { initRateState, checkAndConsume } from "./store/rate";
import { updateCritic } from "./store/critic";
import { loadEnv } from "./config/env";
import { sanitizeErrorMessage } from "./audit/filter";

type Scope = "session" | "project" | "principle";

// サーバー情報
const SERVER_NAME = "@pce/memory";
const SERVER_VERSION = "0.1.0";

let currentPolicy: BoundaryPolicy = defaultPolicy.boundary;
let currentPolicyVersion = defaultPolicy.version ?? "0.1";

function validateString(field: string, val: any, max: number) {
  if (typeof val !== "string" || val.length === 0 || val.length > max) {
    throw new Error(`INVALID_${field.toUpperCase()}`);
  }
}

type ErrorCode =
  | "POLICY_INVALID"
  | "UPSERT_FAILED"
  | "ACTIVATE_FAILED"
  | "BOUNDARY_ERROR"
  | "FEEDBACK_FAILED"
  | "VALIDATION_ERROR"
  | "RATE_LIMIT";

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
      await appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      await appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("POLICY_INVALID", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.upsert", async (req) => {
    const { text, kind, scope, boundary_class, content_hash } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!(await checkAndConsume("tool"))) return { ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId };
      if (!text || !kind || !scope || !boundary_class || !content_hash) {
        return { ...err("VALIDATION_ERROR", "missing fields", reqId), trace_id: traceId };
      }
      validateString("text", text, 5000);
      validateString("kind", kind, 128);
      validateString("boundary_class", boundary_class, 128);
      if (!currentPolicy.boundary_classes[boundary_class]) {
        return { ...err("VALIDATION_ERROR", "unknown boundary_class", reqId), trace_id: traceId };
      }
      const claim = await upsertClaim({ text, kind, scope, boundary_class, content_hash });
      await appendLog({ id: `log_${reqId}`, op: "upsert", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { id: claim.id, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      await appendLog({ id: `log_${reqId}`, op: "upsert", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("UPSERT_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.activate", async (req) => {
    const { scope, allow, top_k, q } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!(await checkAndConsume("activate"))) return { ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId };
      if (!Array.isArray(scope) || !Array.isArray(allow)) return { ...err("VALIDATION_ERROR", "scope/allow must be arrays", reqId), trace_id: traceId };
      const invalidScope = scope.some((s: string) => !["session", "project", "principle"].includes(s));
      if (invalidScope) return { ...err("VALIDATION_ERROR", "unknown scope", reqId), trace_id: traceId };
      if (allow.some((a: any) => typeof a !== "string")) return { ...err("VALIDATION_ERROR", "allow must be string[]", reqId), trace_id: traceId };
      const claims: Claim[] = await listClaimsByScope(scope, top_k ?? 12, q);
      const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
      await saveActiveContext({ id: acId, claims });
      await appendLog({ id: `log_${reqId}`, op: "activate", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { active_context_id: acId, claims, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      await appendLog({ id: `log_${reqId}`, op: "activate", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("ACTIVATE_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.boundary.validate", async (req) => {
    const { payload, allow, scope } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      const res = boundaryValidate({ payload, allow, scope }, currentPolicy);
      await appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: res.allowed, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      await appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("BOUNDARY_ERROR", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });

  server.setRequestHandler("pce.memory.feedback", async (req) => {
    const { claim_id, signal, score } = req.params as any;
    const reqId = crypto.randomUUID();
    const traceId = crypto.randomUUID();
    try {
      if (!(await checkAndConsume("tool"))) return { ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId };
      if (!claim_id || !signal) return { ...err("VALIDATION_ERROR", "claim_id/signal required", reqId), trace_id: traceId };
      const exists = await findClaimById(claim_id);
      if (!exists) return { ...err("VALIDATION_ERROR", "claim not found", reqId), trace_id: traceId };
      const res = await recordFeedback({ claim_id, signal, score });
      // critic update: helpful +1, harmful -1, outdated -0.5
      const delta = signal === "helpful" ? 1 : signal === "harmful" ? -1 : -0.5;
      await updateCritic(claim_id, delta, 0, 5);
      await appendLog({ id: `log_${reqId}`, op: "feedback", ok: true, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...res, policy_version: currentPolicyVersion, request_id: reqId, trace_id: traceId };
    } catch (e: any) {
      await appendLog({ id: `log_${reqId}`, op: "feedback", ok: false, req: reqId, trace: traceId, policy_version: currentPolicyVersion });
      return { ...err("FEEDBACK_FAILED", e.message ?? String(e), reqId), trace_id: traceId };
    }
  });
}

// ツール定義（ListTools用）
const TOOL_DEFINITIONS = [
  {
    name: "pce.memory.policy.apply",
    description: "ポリシーの適用（不変量・用途タグ・redactルール）",
    inputSchema: {
      type: "object",
      properties: {
        yaml: { type: "string", description: "ポリシーYAML（省略時はデフォルト）" },
      },
    },
  },
  {
    name: "pce.memory.upsert",
    description: "重要な断片（Claim）を登録。由来（provenance）必須",
    inputSchema: {
      type: "object",
      properties: {
        text: { type: "string" },
        kind: { type: "string", enum: ["fact", "preference", "task", "policy_hint"] },
        scope: { type: "string", enum: ["session", "project", "principle"] },
        boundary_class: { type: "string", enum: ["public", "internal", "pii", "secret"] },
        content_hash: { type: "string", pattern: "^sha256:[0-9a-f]{64}$" },
      },
      required: ["text", "kind", "scope", "boundary_class", "content_hash"],
    },
  },
  {
    name: "pce.memory.activate",
    description: "クエリとポリシーに基づきアクティブコンテキスト（AC）を構成",
    inputSchema: {
      type: "object",
      properties: {
        scope: { type: "array", items: { type: "string", enum: ["session", "project", "principle"] } },
        allow: { type: "array", items: { type: "string" } },
        top_k: { type: "integer", minimum: 1, maximum: 50 },
        q: { type: "string", description: "検索クエリ文字列（部分一致）" },
      },
      required: ["scope", "allow"],
    },
  },
  {
    name: "pce.memory.boundary.validate",
    description: "生成前に境界チェック／Redact-before-Send",
    inputSchema: {
      type: "object",
      properties: {
        payload: { type: "string" },
        allow: { type: "array", items: { type: "string" } },
        scope: { type: "string", enum: ["session", "project", "principle"] },
      },
      required: ["payload"],
    },
  },
  {
    name: "pce.memory.feedback",
    description: "採用/棄却/陳腐化/重複のシグナルでCriticを更新",
    inputSchema: {
      type: "object",
      properties: {
        claim_id: { type: "string" },
        signal: { type: "string", enum: ["helpful", "harmful", "outdated", "duplicate"] },
        score: { type: "number", minimum: -1, maximum: 1 },
      },
      required: ["claim_id", "signal"],
    },
  },
];

async function main() {
  // 環境変数読み込み
  const env = loadEnv();

  // 監査ログファイルパスを設定
  setAuditLogPath(env.AUDIT_LOG_PATH);

  // DB初期化（非同期）
  await initDb();
  await initSchema();
  await initRateState();

  // サーバー作成（名前とバージョンを指定）
  const server = new Server(
    { name: SERVER_NAME, version: SERVER_VERSION },
    { capabilities: { tools: {} } }
  );

  // ListToolsハンドラ登録
  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return { tools: TOOL_DEFINITIONS };
  });

  // ツールハンドラ登録
  await registerTools(server);

  // トランスポート接続
  const transport = new StdioServerTransport();
  await server.connect(transport);

  // Graceful shutdown ハンドラ
  const shutdown = async (signal: string) => {
    console.error(`[${SERVER_NAME}] Received ${signal}, shutting down...`);
    try {
      await server.close();
    } catch (e) {
      console.error(`[${SERVER_NAME}] Error during shutdown:`, sanitizeErrorMessage(e));
    }
    process.exit(0);
  };

  process.on("SIGINT", () => shutdown("SIGINT"));
  process.on("SIGTERM", () => shutdown("SIGTERM"));
}

main().catch((err) => {
  console.error(`[${SERVER_NAME}] Fatal error:`, sanitizeErrorMessage(err));
  process.exit(1);
});

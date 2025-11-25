/**
 * PCE Memory MCP Server (stdio)
 * 本番用の最小実装: DuckDB ストア + ポリシー適用 + 境界チェック + upsert/activate/feedback
 *
 * ADR-0002に基づく状態機械APIパターンを採用:
 * - 実行時状態検証により不正な操作順序を防止
 * - Uninitialized → PolicyApplied → HasClaims → Ready の遷移を強制
 * - PCEMemoryクラスを直接使用（StateManager廃止）
 */
import { Server } from "@modelcontextprotocol/sdk/server/index.js";
import { StdioServerTransport } from "@modelcontextprotocol/sdk/server/stdio.js";
import {
  ListToolsRequestSchema,
  CallToolRequestSchema,
} from "@modelcontextprotocol/sdk/types.js";
import { boundaryValidate } from "@pce/boundary";
import { initDb, initSchema } from "./db/connection.js";
import { upsertClaim, listClaimsByScope, findClaimById } from "./store/claims.js";
import type { Claim } from "./store/claims.js";
import { saveActiveContext } from "./store/activeContext.js";
import { recordFeedback } from "./store/feedback.js";
import { appendLog, setAuditLogPath } from "./store/logs.js";
import { initRateState, checkAndConsume } from "./store/rate.js";
import { updateCritic } from "./store/critic.js";
import { loadEnv } from "./config/env.js";
import { sanitizeErrorMessage } from "./audit/filter.js";
import { stateError } from "./domain/stateMachine.js";
import type { ErrorCode } from "./domain/errors.js";
import * as E from "fp-ts/Either";

// memoryState モジュールから状態管理関数をインポート
import {
  initMemoryState,
  applyPolicyOp,
  getPolicy,
  getPolicyVersion,
  getStateType,
  getStateSummary,
  canDoUpsert,
  canDoActivate,
  canDoFeedback,
  transitionToHasClaims,
  transitionToReady,
} from "./state/memoryState.js";

// サーバー情報
const SERVER_NAME = "@pce/memory";
const SERVER_VERSION = "0.1.0";

function validateString(field: string, val: unknown, max: number) {
  if (typeof val !== "string" || val.length === 0 || val.length > max) {
    throw new Error(`INVALID_${field.toUpperCase()}`);
  }
}

function err(code: ErrorCode, message: string, request_id: string) {
  return { error: { code, message }, request_id };
}

/**
 * ツールハンドラの実装（内部用）
 * memoryStateモジュールを使用してエラーハンドリングと永続化を統合
 */
async function handlePolicyApply(args: Record<string, unknown>) {
  const yaml = args?.["yaml"] as string | undefined;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  const result = await applyPolicyOp(yaml)();

  if (E.isLeft(result)) {
    await appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ ...err(result.left.code, result.left.message, reqId), trace_id: traceId }) }], isError: true };
  }

  await appendLog({ id: `log_${reqId}`, op: "policy.apply", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
  return { content: [{ type: "text", text: JSON.stringify({ ...result.right, request_id: reqId, trace_id: traceId }) }] };
}

async function handleUpsert(args: Record<string, unknown>) {
  const { text, kind, scope, boundary_class, content_hash } = args as Record<string, string>;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    // 状態検証: PolicyApplied または HasClaims からのみ呼び出し可能
    if (!canDoUpsert()) {
      const error = stateError("PolicyApplied or HasClaims", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }
    if (!text || !kind || !scope || !boundary_class || !content_hash) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "missing fields", reqId), trace_id: traceId }) }], isError: true };
    }
    validateString("text", text, 5000);
    validateString("kind", kind, 128);
    validateString("boundary_class", boundary_class, 128);
    const policy = getPolicy();
    if (!policy.boundary_classes[boundary_class]) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "unknown boundary_class", reqId), trace_id: traceId }) }], isError: true };
    }
    const { claim, isNew } = await upsertClaim({ text, kind, scope, boundary_class, content_hash });

    // 状態遷移: PolicyApplied | HasClaims → HasClaims
    // 新規挿入の場合のみclaimCountを増加
    transitionToHasClaims(isNew);

    await appendLog({ id: `log_${reqId}`, op: "upsert", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ id: claim.id, is_new: isNew, policy_version: getPolicyVersion(), state: getStateType(), request_id: reqId, trace_id: traceId }) }] };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "upsert", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("UPSERT_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

async function handleActivate(args: Record<string, unknown>) {
  const { scope, allow, top_k, q } = args as { scope?: unknown; allow?: unknown; top_k?: number; q?: string };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    // 状態検証: HasClaims または Ready からのみ呼び出し可能
    if (!canDoActivate()) {
      const error = stateError("HasClaims or Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    if (!(await checkAndConsume("activate"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }
    if (!Array.isArray(scope) || !Array.isArray(allow)) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "scope/allow must be arrays", reqId), trace_id: traceId }) }], isError: true };
    }
    const invalidScope = scope.some((s: string) => !["session", "project", "principle"].includes(s));
    if (invalidScope) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "unknown scope", reqId), trace_id: traceId }) }], isError: true };
    }
    if (allow.some((a: unknown) => typeof a !== "string")) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "allow must be string[]", reqId), trace_id: traceId }) }], isError: true };
    }
    const claims: Claim[] = await listClaimsByScope(scope, top_k ?? 12, q);
    const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
    await saveActiveContext({ id: acId, claims });

    // 状態遷移: HasClaims | Ready → Ready
    transitionToReady(acId);

    await appendLog({ id: `log_${reqId}`, op: "activate", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ active_context_id: acId, claims, policy_version: getPolicyVersion(), state: getStateType(), request_id: reqId, trace_id: traceId }) }] };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "activate", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("ACTIVATE_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

async function handleBoundaryValidate(args: Record<string, unknown>) {
  const { payload, allow, scope } = args as { payload?: string; allow?: string[]; scope?: string };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    const policy = getPolicy();
    const res = boundaryValidate({ payload: payload ?? "", allow: allow ?? [], scope: scope ?? "" }, policy);
    await appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: res.allowed, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ ...res, policy_version: getPolicyVersion(), request_id: reqId, trace_id: traceId }) }] };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "boundary.validate", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("BOUNDARY_ERROR", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

async function handleFeedback(args: Record<string, unknown>) {
  const { claim_id, signal, score } = args as { claim_id?: string; signal?: string; score?: number };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    // 状態検証: Ready からのみ呼び出し可能
    if (!canDoFeedback()) {
      const error = stateError("Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }
    if (!claim_id || !signal) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "claim_id/signal required", reqId), trace_id: traceId }) }], isError: true };
    }
    const exists = await findClaimById(claim_id);
    if (!exists) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "claim not found", reqId), trace_id: traceId }) }], isError: true };
    }
    const feedbackInput: { claim_id: string; signal: "helpful" | "harmful" | "outdated" | "duplicate"; score?: number } = {
      claim_id,
      signal: signal as "helpful" | "harmful" | "outdated" | "duplicate",
    };
    if (score !== undefined) {
      feedbackInput.score = score;
    }
    const res = await recordFeedback(feedbackInput);
    // critic update: helpful +1, harmful -1, outdated -0.5, duplicate -0.5
    const delta = signal === "helpful" ? 1 : signal === "harmful" ? -1 : -0.5;
    await updateCritic(claim_id, delta, 0, 5);

    // Ready状態は維持（feedback後もReady）
    await appendLog({ id: `log_${reqId}`, op: "feedback", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ ...res, policy_version: getPolicyVersion(), state: getStateType(), request_id: reqId, trace_id: traceId }) }] };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "feedback", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("FEEDBACK_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

/**
 * 現在の状態機械の状態を取得
 * 本番環境ではruntime_stateの詳細を露出しない（デバッグ用フラグで制御）
 */
async function handleGetState(args: Record<string, unknown>) {
  const includeDetails = args?.["debug"] === true;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  return {
    content: [{
      type: "text",
      text: JSON.stringify({
        ...getStateSummary(includeDetails),
        request_id: reqId,
        trace_id: traceId
      })
    }]
  };
}

/**
 * MCP ツールハンドラの登録（CallToolRequestSchema を使用）
 */
async function registerTools(server: Server) {
  // CallToolRequestSchema を使用してツール呼び出しをディスパッチ
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;
    const toolArgs = (args ?? {}) as Record<string, unknown>;

    switch (name) {
      case "pce.memory.policy.apply":
        return handlePolicyApply(toolArgs);
      case "pce.memory.upsert":
        return handleUpsert(toolArgs);
      case "pce.memory.activate":
        return handleActivate(toolArgs);
      case "pce.memory.boundary.validate":
        return handleBoundaryValidate(toolArgs);
      case "pce.memory.feedback":
        return handleFeedback(toolArgs);
      case "pce.memory.state":
        return handleGetState(toolArgs);
      default:
        return { content: [{ type: "text", text: JSON.stringify({ error: { code: "UNKNOWN_TOOL", message: `Unknown tool: ${name}` } }) }], isError: true };
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
  {
    name: "pce.memory.state",
    description: "現在の状態機械の状態を取得（Uninitialized/PolicyApplied/HasClaims/Ready）",
    inputSchema: {
      type: "object",
      properties: {
        debug: { type: "boolean", description: "デバッグ用: runtime_stateの詳細を含める（デフォルト: false）" },
      },
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

  // 状態復元: memoryStateモジュールの初期化
  // DBからポリシーとclaim数を読み込み、適切な状態に復元
  const initResult = await initMemoryState()();
  if (E.isLeft(initResult)) {
    console.error(`[${SERVER_NAME}] Failed to initialize state: ${initResult.left.message}`);
    // 初期化失敗時はUninitializedのまま起動（policy.applyで初期化可能）
  } else {
    console.error(`[${SERVER_NAME}] Restored state: ${initResult.right.state} (policy: ${initResult.right.policyVersion})`);
  }

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

/**
 * MCP Tool Handlers（コア実装）
 *
 * デーモンモード/stdioモード両方から利用可能なハンドラ実装。
 * index.tsから抽出し、再利用可能にした。
 */

import { boundaryValidate } from "@pce/boundary";
import { upsertClaim, upsertClaimWithEmbedding, findClaimById } from "../store/claims.js";
import type { Provenance } from "../store/claims.js";
import { hybridSearchPaginated, getEmbeddingService } from "../store/hybridSearch.js";
import { upsertEntity, linkClaimEntity } from "../store/entities.js";
import type { EntityInput } from "../store/entities.js";
import { upsertRelation } from "../store/relations.js";
import type { RelationInput } from "../store/relations.js";
import { getEvidenceForClaims } from "../store/evidence.js";
import type { Evidence } from "../store/evidence.js";
import { saveActiveContext } from "../store/activeContext.js";
import { recordFeedback } from "../store/feedback.js";
import { appendLog } from "../store/logs.js";
import { checkAndConsume } from "../store/rate.js";
import { updateCritic } from "../store/critic.js";
import { stateError } from "../domain/stateMachine.js";
import type { ErrorCode } from "../domain/errors.js";
import * as E from "fp-ts/Either";

import {
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
} from "../state/memoryState.js";

import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
  addResourceToCurrentScope,
  getLayerScopeSummary,
} from "../state/layerScopeState.js";
import { safeJsonStringify } from "../utils/serialization.js";

// ========== Utility Functions ==========

function validateString(field: string, val: unknown, max: number) {
  if (typeof val !== "string" || val.length === 0 || val.length > max) {
    throw new Error(`INVALID_${field.toUpperCase()}`);
  }
}

function err(code: ErrorCode, message: string, request_id: string) {
  return { error: { code, message }, request_id };
}

// ========== Upsert Helper Functions ==========

/**
 * Upsertの入力バリデーション
 * 状態検証、レート制限、フィールド検証を実行
 */
interface UpsertValidationResult {
  isValid: boolean;
  errorResponse?: { content: Array<{ type: string; text: string }>; isError: boolean };
}

async function validateUpsertInput(
  args: {
    text: string | undefined;
    kind: string | undefined;
    scope: string | undefined;
    boundary_class: string | undefined;
    content_hash: string | undefined;
  },
  scopeId: string,
  reqId: string,
  traceId: string
): Promise<UpsertValidationResult> {
  const { text, kind, scope, boundary_class, content_hash } = args;

  // 状態検証
  if (!canDoUpsert()) {
    const error = stateError("PolicyApplied or HasClaims", getStateType());
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true }
    };
  }

  if (!isInActiveScope(scopeId)) {
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", "scope not active", reqId), trace_id: traceId }) }], isError: true }
    };
  }

  if (!(await checkAndConsume("tool"))) {
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true }
    };
  }

  if (!text || !kind || !scope || !boundary_class || !content_hash) {
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "missing fields", reqId), trace_id: traceId }) }], isError: true }
    };
  }

  try {
    validateString("text", text, 5000);
    validateString("kind", kind, 128);
    validateString("boundary_class", boundary_class, 128);
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", msg, reqId), trace_id: traceId }) }], isError: true }
    };
  }

  const policy = getPolicy();
  if (!policy.boundary_classes[boundary_class]) {
    return {
      isValid: false,
      errorResponse: { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "unknown boundary_class", reqId), trace_id: traceId }) }], isError: true }
    };
  }

  return { isValid: true };
}

/**
 * Graph Memory（Entity/Relation）の処理
 * 新規Claimに対してのみentities/relationsを登録
 */
interface GraphMemoryResult {
  entityCount: number;
  entityFailed: number;
  relationCount: number;
  relationFailed: number;
}

async function processGraphMemory(
  claimId: string,
  isNew: boolean,
  entities: EntityInput[] | undefined,
  relations: RelationInput[] | undefined
): Promise<GraphMemoryResult> {
  let entityCount = 0;
  let entityFailed = 0;
  let relationCount = 0;
  let relationFailed = 0;

  if (isNew && entities && Array.isArray(entities)) {
    for (const entity of entities) {
      try {
        await upsertEntity(entity);
        await linkClaimEntity(claimId, entity.id);
        entityCount++;
      } catch {
        entityFailed++;
      }
    }
  }

  if (isNew && relations && Array.isArray(relations)) {
    for (const relation of relations) {
      try {
        await upsertRelation(relation);
        relationCount++;
      } catch {
        relationFailed++;
      }
    }
  }

  return { entityCount, entityFailed, relationCount, relationFailed };
}

// ========== Handler Implementations ==========

export async function handlePolicyApply(args: Record<string, unknown>) {
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

export async function handleUpsert(args: Record<string, unknown>) {
  const { text, kind, scope, boundary_class, content_hash, provenance, entities, relations } = args as {
    text?: string;
    kind?: string;
    scope?: string;
    boundary_class?: string;
    content_hash?: string;
    provenance?: Provenance;
    entities?: EntityInput[];
    relations?: RelationInput[];
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  // TLA+ EnterScope: リクエストスコープを開始
  const scopeResult = enterRequestScope(reqId);
  if (E.isLeft(scopeResult)) {
    return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", scopeResult.left.message, reqId), trace_id: traceId }) }], isError: true };
  }
  const scopeId = scopeResult.right;

  try {
    // バリデーション（ヘルパー関数に委譲）
    const validation = await validateUpsertInput(
      { text, kind, scope, boundary_class, content_hash },
      scopeId,
      reqId,
      traceId
    );
    if (!validation.isValid) {
      return validation.errorResponse!;
    }

    // Claim登録（EmbeddingServiceがあれば埋め込みも生成）
    const claimInput = {
      text: text!,
      kind: kind!,
      scope: scope!,
      boundary_class: boundary_class!,
      content_hash: content_hash!,
      ...(provenance !== undefined ? { provenance } : {}),
    };
    const embeddingService = getEmbeddingService();
    const { claim, isNew } = embeddingService
      ? await upsertClaimWithEmbedding(claimInput, embeddingService)
      : await upsertClaim(claimInput);

    // Graph Memory処理（ヘルパー関数に委譲）
    const graphResult = await processGraphMemory(claim.id, isNew, entities, relations);

    // スコープへのリソース登録
    const addResult = addResourceToCurrentScope(scopeId, claim.id);
    if (E.isLeft(addResult)) {
      console.error(`[Handler] Failed to add resource to scope: ${addResult.left.message}`);
    }

    // 状態遷移
    transitionToHasClaims(isNew);

    // 監査ログ記録
    await appendLog({ id: `log_${reqId}`, op: "upsert", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });

    // レスポンス構築
    const { entityCount, entityFailed, relationCount, relationFailed } = graphResult;
    const graphMemoryResult = (entityCount > 0 || entityFailed > 0 || relationCount > 0 || relationFailed > 0)
      ? {
          graph_memory: {
            entities: { success: entityCount, failed: entityFailed },
            relations: { success: relationCount, failed: relationFailed },
          }
        }
      : {};

    return {
      content: [{
        type: "text",
        text: JSON.stringify({
          id: claim.id,
          is_new: isNew,
          ...graphMemoryResult,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "upsert", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("UPSERT_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  } finally {
    exitRequestScope(scopeId);
  }
}

export async function handleActivate(args: Record<string, unknown>) {
  const { scope, allow, top_k, q, cursor, include_meta } = args as {
    scope?: unknown;
    allow?: unknown;
    top_k?: number;
    q?: string;
    cursor?: string;
    include_meta?: boolean;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
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

    const searchConfig = cursor !== undefined ? { cursor } : {};
    const searchResult = await hybridSearchPaginated(scope, top_k ?? 12, q, searchConfig);
    const claims = searchResult.results.map((r) => r.claim);
    const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
    await saveActiveContext({ id: acId, claims });

    let evidenceMap: Map<string, Evidence[]> | undefined;
    if (include_meta && claims.length > 0) {
      const claimIds = claims.map((c) => c.id);
      evidenceMap = await getEvidenceForClaims(claimIds);
    }

    const scoredItems = searchResult.results.map((r) => ({
      claim: r.claim,
      score: r.score,
      evidences: evidenceMap?.get(r.claim.id) ?? [],
    }));

    transitionToReady(acId);

    await appendLog({ id: `log_${reqId}`, op: "activate", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return {
      content: [{
        type: "text",
        text: safeJsonStringify({
          active_context_id: acId,
          claims: scoredItems,
          claims_count: claims.length,
          next_cursor: searchResult.next_cursor,
          has_more: searchResult.has_more,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "activate", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("ACTIVATE_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

export async function handleBoundaryValidate(args: Record<string, unknown>) {
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

export async function handleFeedback(args: Record<string, unknown>) {
  const { claim_id, signal, score } = args as { claim_id?: string; signal?: string; score?: number };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
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
    const delta = signal === "helpful" ? 1 : signal === "harmful" ? -1 : -0.5;
    await updateCritic(claim_id, delta, 0, 5);

    await appendLog({ id: `log_${reqId}`, op: "feedback", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    return { content: [{ type: "text", text: JSON.stringify({ ...res, policy_version: getPolicyVersion(), state: getStateType(), request_id: reqId, trace_id: traceId }) }] };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "feedback", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("FEEDBACK_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

export async function handleGetState(args: Record<string, unknown>) {
  const includeDetails = args?.["debug"] === true;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  const summary = getStateSummary(includeDetails);
  const layerScopeSummary = includeDetails ? getLayerScopeSummary() : undefined;

  return {
    content: [{
      type: "text",
      text: JSON.stringify({
        ...summary,
        ...(layerScopeSummary ? { layer_scope: layerScopeSummary } : {}),
        request_id: reqId,
        trace_id: traceId
      })
    }]
  };
}

// ========== Tool Dispatcher ==========

export type ToolResult = {
  content: Array<{ type: string; text: string }>;
  isError?: boolean;
};

/**
 * ツール名に基づいてハンドラをディスパッチ
 */
export async function dispatchTool(name: string, args: Record<string, unknown>): Promise<ToolResult> {
  switch (name) {
    case "pce.memory.policy.apply":
      return handlePolicyApply(args);
    case "pce.memory.upsert":
      return handleUpsert(args);
    case "pce.memory.activate":
      return handleActivate(args);
    case "pce.memory.boundary.validate":
      return handleBoundaryValidate(args);
    case "pce.memory.feedback":
      return handleFeedback(args);
    case "pce.memory.state":
      return handleGetState(args);
    default:
      return {
        content: [{ type: "text", text: JSON.stringify({ error: { code: "UNKNOWN_TOOL", message: `Unknown tool: ${name}` } }) }],
        isError: true
      };
  }
}

// ========== Tool Definitions ==========

export const TOOL_DEFINITIONS = [
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
        provenance: {
          type: "object",
          properties: {
            at: { type: "string", format: "date-time" },
            actor: { type: "string" },
            git: {
              type: "object",
              properties: {
                commit: { type: "string" },
                repo: { type: "string" },
                url: { type: "string" },
                files: { type: "array", items: { type: "string" } },
              },
            },
            url: { type: "string" },
            note: { type: "string" },
            signed: { type: "boolean" },
          },
          required: ["at"],
        },
        entities: {
          type: "array",
          items: {
            type: "object",
            properties: {
              id: { type: "string" },
              type: { type: "string", enum: ["Actor", "Artifact", "Event", "Concept"] },
              name: { type: "string" },
              canonical_key: { type: "string" },
              attrs: { type: "object" },
            },
            required: ["id", "type", "name"],
          },
        },
        relations: {
          type: "array",
          items: {
            type: "object",
            properties: {
              id: { type: "string" },
              src_id: { type: "string" },
              dst_id: { type: "string" },
              type: { type: "string" },
              props: { type: "object" },
              evidence_claim_id: { type: "string" },
            },
            required: ["id", "src_id", "dst_id", "type"],
          },
        },
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
        cursor: { type: "string", description: "ページネーション用カーソル" },
        include_meta: { type: "boolean", description: "メタ情報（evidence等）を含める", default: false },
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

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
import { upsertEntity, linkClaimEntity, queryEntities } from "../store/entities.js";
import type { EntityInput, EntityQueryFilters } from "../store/entities.js";
import { upsertRelation, queryRelations } from "../store/relations.js";
import type { RelationInput, RelationQueryFilters } from "../store/relations.js";
import { getEvidenceForClaims } from "../store/evidence.js";
import type { Evidence } from "../store/evidence.js";
import { saveActiveContext } from "../store/activeContext.js";
import { recordFeedback } from "../store/feedback.js";
import { appendLog } from "../store/logs.js";
import { checkAndConsume } from "../store/rate.js";
import { updateCritic } from "../store/critic.js";
import { stateError } from "../domain/stateMachine.js";
import type { ErrorCode } from "../domain/errors.js";
import { ENTITY_TYPES, isValidEntityType } from "../domain/types.js";
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
  canDoQuery,
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

// ========== Graph Memory Handlers ==========

export async function handleUpsertEntity(args: Record<string, unknown>) {
  const { id, type, name, canonical_key, attrs } = args as {
    id?: string;
    type?: string;
    name?: string;
    canonical_key?: string;
    attrs?: Record<string, unknown>;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoUpsert()) {
      const error = stateError("PolicyApplied or HasClaims or Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    // レート制限チェック
    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }

    // バリデーション
    if (!id || !type || !name) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "id, type, name are required", reqId), trace_id: traceId }) }], isError: true };
    }

    if (!isValidEntityType(type)) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", `type must be one of: ${ENTITY_TYPES.join(", ")}`, reqId), trace_id: traceId }) }], isError: true };
    }

    // 文字列長バリデーション
    try {
      validateString("id", id, 256);
      validateString("name", name, 1024);
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", msg, reqId), trace_id: traceId }) }], isError: true };
    }

    // Entity登録（exactOptionalPropertyTypes対応: undefinedを渡さない）
    const entity = await upsertEntity({
      id,
      type: type as "Actor" | "Artifact" | "Event" | "Concept",
      name,
      ...(canonical_key !== undefined && { canonical_key }),
      ...(attrs !== undefined && { attrs }),
    });

    await appendLog({ id: `log_${reqId}`, op: "upsert_entity", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });

    return {
      content: [{
        type: "text",
        text: JSON.stringify({
          id: entity.id,
          type: entity.type,
          name: entity.name,
          canonical_key: entity.canonical_key,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "upsert_entity", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("UPSERT_ENTITY_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

export async function handleUpsertRelation(args: Record<string, unknown>) {
  const { id, src_id, dst_id, type, props, evidence_claim_id } = args as {
    id?: string;
    src_id?: string;
    dst_id?: string;
    type?: string;
    props?: Record<string, unknown>;
    evidence_claim_id?: string;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoUpsert()) {
      const error = stateError("PolicyApplied or HasClaims or Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    // レート制限チェック
    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }

    // バリデーション
    if (!id || !src_id || !dst_id || !type) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "id, src_id, dst_id, type are required", reqId), trace_id: traceId }) }], isError: true };
    }

    // 文字列長バリデーション
    try {
      validateString("id", id, 256);
      validateString("src_id", src_id, 256);
      validateString("dst_id", dst_id, 256);
      validateString("type", type, 256);
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", msg, reqId), trace_id: traceId }) }], isError: true };
    }

    // Relation登録（exactOptionalPropertyTypes対応: undefinedを渡さない）
    const relation = await upsertRelation({
      id,
      src_id,
      dst_id,
      type,
      ...(props !== undefined && { props }),
      ...(evidence_claim_id !== undefined && { evidence_claim_id }),
    });

    await appendLog({ id: `log_${reqId}`, op: "upsert_relation", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });

    return {
      content: [{
        type: "text",
        text: JSON.stringify({
          id: relation.id,
          src_id: relation.src_id,
          dst_id: relation.dst_id,
          type: relation.type,
          evidence_claim_id: relation.evidence_claim_id,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "upsert_relation", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: JSON.stringify({ ...err("UPSERT_RELATION_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

export async function handleQueryEntity(args: Record<string, unknown>) {
  const { id, type, canonical_key, claim_id, limit } = args as {
    id?: string;
    type?: string;
    canonical_key?: string;
    claim_id?: string;
    limit?: number;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError("PolicyApplied or HasClaims or Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    // レート制限チェック
    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter = id !== undefined || type !== undefined || canonical_key !== undefined || claim_id !== undefined;
    if (!hasFilter) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "at least one filter (id, type, canonical_key, claim_id) is required", reqId), trace_id: traceId }) }], isError: true };
    }

    // typeのバリデーション
    if (type !== undefined && !isValidEntityType(type)) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", `type must be one of: ${ENTITY_TYPES.join(", ")}`, reqId), trace_id: traceId }) }], isError: true };
    }

    // クエリ実行
    const filters: EntityQueryFilters = {
      ...(id !== undefined && { id }),
      ...(type !== undefined && { type: type as "Actor" | "Artifact" | "Event" | "Concept" }),
      ...(canonical_key !== undefined && { canonical_key }),
      ...(claim_id !== undefined && { claim_id }),
      ...(limit !== undefined && { limit }),
    };
    const entities = await queryEntities(filters);

    await appendLog({ id: `log_${reqId}`, op: "query_entity", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return {
      content: [{
        type: "text",
        text: safeJsonStringify({
          entities,
          count: entities.length,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "query_entity", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: safeJsonStringify({ ...err("QUERY_ENTITY_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
  }
}

export async function handleQueryRelation(args: Record<string, unknown>) {
  const { id, src_id, dst_id, type, evidence_claim_id, limit } = args as {
    id?: string;
    src_id?: string;
    dst_id?: string;
    type?: string;
    evidence_claim_id?: string;
    limit?: number;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError("PolicyApplied or HasClaims or Ready", getStateType());
      return { content: [{ type: "text", text: JSON.stringify({ ...err("STATE_ERROR", error.message, reqId), trace_id: traceId }) }], isError: true };
    }

    // レート制限チェック
    if (!(await checkAndConsume("tool"))) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("RATE_LIMIT", "rate limit exceeded", reqId), trace_id: traceId }) }], isError: true };
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter = id !== undefined || src_id !== undefined || dst_id !== undefined || type !== undefined || evidence_claim_id !== undefined;
    if (!hasFilter) {
      return { content: [{ type: "text", text: JSON.stringify({ ...err("VALIDATION_ERROR", "at least one filter (id, src_id, dst_id, type, evidence_claim_id) is required", reqId), trace_id: traceId }) }], isError: true };
    }

    // クエリ実行
    const filters: RelationQueryFilters = {
      ...(id !== undefined && { id }),
      ...(src_id !== undefined && { src_id }),
      ...(dst_id !== undefined && { dst_id }),
      ...(type !== undefined && { type }),
      ...(evidence_claim_id !== undefined && { evidence_claim_id }),
      ...(limit !== undefined && { limit }),
    };
    const relations = await queryRelations(filters);

    await appendLog({ id: `log_${reqId}`, op: "query_relation", ok: true, req: reqId, trace: traceId, policy_version: getPolicyVersion() });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return {
      content: [{
        type: "text",
        text: safeJsonStringify({
          relations,
          count: relations.length,
          policy_version: getPolicyVersion(),
          state: getStateType(),
          request_id: reqId,
          trace_id: traceId
        })
      }]
    };
  } catch (e: unknown) {
    await appendLog({ id: `log_${reqId}`, op: "query_relation", ok: false, req: reqId, trace: traceId, policy_version: getPolicyVersion() });
    const msg = e instanceof Error ? e.message : String(e);
    return { content: [{ type: "text", text: safeJsonStringify({ ...err("QUERY_RELATION_FAILED", msg, reqId), trace_id: traceId }) }], isError: true };
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
    case "pce.memory.upsert.entity":
      return handleUpsertEntity(args);
    case "pce.memory.upsert.relation":
      return handleUpsertRelation(args);
    case "pce.memory.query.entity":
      return handleQueryEntity(args);
    case "pce.memory.query.relation":
      return handleQueryRelation(args);
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
    description: "Apply policy (invariants, usage tags, redact rules)",
    inputSchema: {
      type: "object",
      properties: {
        yaml: { type: "string", description: "Policy YAML (uses default if omitted)" },
      },
    },
  },
  {
    name: "pce.memory.upsert",
    description: "Register a claim (knowledge fragment). Provenance required",
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
    description: "Build active context (AC) based on query and policy",
    inputSchema: {
      type: "object",
      properties: {
        scope: { type: "array", items: { type: "string", enum: ["session", "project", "principle"] } },
        allow: { type: "array", items: { type: "string" } },
        top_k: { type: "integer", minimum: 1, maximum: 50 },
        q: { type: "string", description: "Search query string (partial match)" },
        cursor: { type: "string", description: "Pagination cursor" },
        include_meta: { type: "boolean", description: "Include metadata (evidence, etc.)", default: false },
      },
      required: ["scope", "allow"],
    },
  },
  {
    name: "pce.memory.boundary.validate",
    description: "Pre-generation boundary check / Redact-before-Send",
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
    description: "Update critic with signal (helpful/harmful/outdated/duplicate)",
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
    description: "Get current state machine status (Uninitialized/PolicyApplied/HasClaims/Ready)",
    inputSchema: {
      type: "object",
      properties: {
        debug: { type: "boolean", description: "Debug mode: include runtime_state details (default: false)" },
      },
    },
  },
  // ========== Graph Memory Tools ==========
  {
    name: "pce.memory.upsert.entity",
    description: "Register an entity in graph memory (Actor/Artifact/Event/Concept)",
    inputSchema: {
      type: "object",
      properties: {
        id: { type: "string", description: "Entity ID" },
        type: { type: "string", enum: ["Actor", "Artifact", "Event", "Concept"], description: "Entity type" },
        name: { type: "string", description: "Entity name" },
        canonical_key: { type: "string", description: "Canonical key (optional, for deduplication)" },
        attrs: { type: "object", description: "Additional attributes (optional)" },
      },
      required: ["id", "type", "name"],
    },
  },
  {
    name: "pce.memory.upsert.relation",
    description: "Register a relation between entities in graph memory",
    inputSchema: {
      type: "object",
      properties: {
        id: { type: "string", description: "Relation ID" },
        src_id: { type: "string", description: "Source entity ID" },
        dst_id: { type: "string", description: "Target entity ID" },
        type: { type: "string", description: "Relation type (e.g., KNOWS, USES, DEPENDS_ON)" },
        props: { type: "object", description: "Additional relation properties (optional)" },
        evidence_claim_id: { type: "string", description: "Claim ID as evidence for this relation (optional)" },
      },
      required: ["id", "src_id", "dst_id", "type"],
    },
  },
  {
    name: "pce.memory.query.entity",
    description: "Query entities from graph memory by ID, type, canonical_key, or claim_id",
    inputSchema: {
      type: "object",
      properties: {
        id: { type: "string", description: "Entity ID (exact match)" },
        type: { type: "string", enum: ["Actor", "Artifact", "Event", "Concept"], description: "Entity type" },
        canonical_key: { type: "string", description: "Canonical key (exact match)" },
        claim_id: { type: "string", description: "Claim ID to find linked entities" },
        limit: { type: "integer", minimum: 1, maximum: 100, description: "Max results (default: 50)" },
      },
    },
  },
  {
    name: "pce.memory.query.relation",
    description: "Query relations from graph memory by ID, src_id, dst_id, type, or evidence_claim_id",
    inputSchema: {
      type: "object",
      properties: {
        id: { type: "string", description: "Relation ID (exact match)" },
        src_id: { type: "string", description: "Source entity ID" },
        dst_id: { type: "string", description: "Target entity ID" },
        type: { type: "string", description: "Relation type (e.g., TAGGED, KNOWS)" },
        evidence_claim_id: { type: "string", description: "Evidence claim ID" },
        limit: { type: "integer", minimum: 1, maximum: 100, description: "Max results (default: 50)" },
      },
    },
  },
];

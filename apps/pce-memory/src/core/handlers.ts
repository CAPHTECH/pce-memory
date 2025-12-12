/**
 * MCP Tool Handlers（コア実装）
 *
 * デーモンモード/stdioモード両方から利用可能なハンドラ実装。
 * index.tsから抽出し、再利用可能にした。
 */

import { boundaryValidate } from '@pce/boundary';
import { upsertClaim, upsertClaimWithEmbedding, findClaimById } from '../store/claims.js';
import type { Provenance } from '../store/claims.js';
import { hybridSearchPaginated, getEmbeddingService } from '../store/hybridSearch.js';
import { upsertEntity, linkClaimEntity, queryEntities } from '../store/entities.js';
import type { EntityInput, EntityQueryFilters } from '../store/entities.js';
import { upsertRelation, queryRelations } from '../store/relations.js';
import type { RelationInput, RelationQueryFilters } from '../store/relations.js';
import { getEvidenceForClaims } from '../store/evidence.js';
import type { Evidence } from '../store/evidence.js';
import { saveActiveContext } from '../store/activeContext.js';
import { recordFeedback } from '../store/feedback.js';
import { appendLog } from '../store/logs.js';
import { checkAndConsume } from '../store/rate.js';
import { updateCritic } from '../store/critic.js';
import { stateError } from '../domain/stateMachine.js';
import type { ErrorCode } from '../domain/errors.js';
import { ENTITY_TYPES, isValidEntityType } from '../domain/types.js';
import * as E from 'fp-ts/Either';

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
} from '../state/memoryState.js';

// Sync機能のインポート
import {
  executePush,
  executePull,
  type PushOptions,
  type PullOptions,
  type Scope,
  type BoundaryClass,
} from '../sync/index.js';

import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
  addResourceToCurrentScope,
  getLayerScopeSummary,
} from '../state/layerScopeState.js';
import { safeJsonStringify } from '../utils/serialization.js';

// ========== Type Definitions ==========

/**
 * MCP Tool Result型
 * structuredContent: MCP outputSchema対応のための構造化データ
 */
export type ToolResult = {
  content: Array<{ type: string; text: string }>;
  structuredContent?: Record<string, unknown>;
  isError?: boolean;
};

/**
 * 統一されたToolResult生成ヘルパー
 * content（後方互換性用テキスト）とstructuredContent（構造化データ）の両方を生成
 */
function createToolResult<T extends Record<string, unknown>>(
  data: T,
  options: { isError?: boolean; useSafeStringify?: boolean } = {}
): ToolResult {
  const text = options.useSafeStringify ? safeJsonStringify(data) : JSON.stringify(data);
  return {
    content: [{ type: 'text', text }],
    structuredContent: data,
    ...(options.isError && { isError: true }),
  };
}

// ========== Utility Functions ==========

function validateString(field: string, val: unknown, max: number) {
  if (typeof val !== 'string' || val.length === 0 || val.length > max) {
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
  errorResponse?: ToolResult;
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
    const error = stateError('PolicyApplied or HasClaims', getStateType());
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!isInActiveScope(scopeId)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('STATE_ERROR', 'scope not active', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!(await checkAndConsume('tool'))) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!text || !kind || !scope || !boundary_class || !content_hash) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'missing fields', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  try {
    validateString('text', text, 5000);
    validateString('kind', kind, 128);
    validateString('boundary_class', boundary_class, 128);
  } catch (e) {
    const msg = e instanceof Error ? e.message : String(e);
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', msg, reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  const policy = getPolicy();
  if (!policy.boundary_classes[boundary_class]) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown boundary_class', reqId), trace_id: traceId },
        { isError: true }
      ),
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
  const yaml = args?.['yaml'] as string | undefined;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  const result = await applyPolicyOp(yaml)();

  if (E.isLeft(result)) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'policy.apply',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    return createToolResult(
      {
        ...err(result.left.code, result.left.message, reqId),
        trace_id: traceId,
      },
      { isError: true }
    );
  }

  await appendLog({
    id: `log_${reqId}`,
    op: 'policy.apply',
    ok: true,
    req: reqId,
    trace: traceId,
    policy_version: getPolicyVersion(),
  });
  return createToolResult({ ...result.right, request_id: reqId, trace_id: traceId });
}

export async function handleUpsert(args: Record<string, unknown>) {
  const { text, kind, scope, boundary_class, content_hash, provenance, entities, relations } =
    args as {
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
    return createToolResult(
      {
        ...err('STATE_ERROR', scopeResult.left.message, reqId),
        trace_id: traceId,
      },
      { isError: true }
    );
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
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    // レスポンス構築
    const { entityCount, entityFailed, relationCount, relationFailed } = graphResult;
    const graphMemoryResult =
      entityCount > 0 || entityFailed > 0 || relationCount > 0 || relationFailed > 0
        ? {
            graph_memory: {
              entities: { success: entityCount, failed: entityFailed },
              relations: { success: relationCount, failed: relationFailed },
            },
          }
        : {};

    return createToolResult({
      id: claim.id,
      is_new: isNew,
      ...graphMemoryResult,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('UPSERT_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
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
      const error = stateError('HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!(await checkAndConsume('activate'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (!Array.isArray(scope) || !Array.isArray(allow)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'scope/allow must be arrays', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const invalidScope = scope.some(
      (s: string) => !['session', 'project', 'principle'].includes(s)
    );
    if (invalidScope) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown scope', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (allow.some((a: unknown) => typeof a !== 'string')) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'allow must be string[]', reqId), trace_id: traceId },
        { isError: true }
      );
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

    await appendLog({
      id: `log_${reqId}`,
      op: 'activate',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        active_context_id: acId,
        claims: scoredItems,
        claims_count: claims.length,
        next_cursor: searchResult.next_cursor,
        has_more: searchResult.has_more,
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'activate',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('ACTIVATE_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

export async function handleBoundaryValidate(args: Record<string, unknown>) {
  const { payload, allow, scope } = args as { payload?: string; allow?: string[]; scope?: string };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    const policy = getPolicy();
    const res = boundaryValidate(
      { payload: payload ?? '', allow: allow ?? [], scope: scope ?? '' },
      policy
    );
    await appendLog({
      id: `log_${reqId}`,
      op: 'boundary.validate',
      ok: res.allowed,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    return createToolResult({
      ...res,
      policy_version: getPolicyVersion(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'boundary.validate',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('BOUNDARY_ERROR', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

export async function handleFeedback(args: Record<string, unknown>) {
  const { claim_id, signal, score } = args as {
    claim_id?: string;
    signal?: string;
    score?: number;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    if (!canDoFeedback()) {
      const error = stateError('Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (!claim_id || !signal) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'claim_id/signal required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const exists = await findClaimById(claim_id);
    if (!exists) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'claim not found', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const feedbackInput: {
      claim_id: string;
      signal: 'helpful' | 'harmful' | 'outdated' | 'duplicate';
      score?: number;
    } = {
      claim_id,
      signal: signal as 'helpful' | 'harmful' | 'outdated' | 'duplicate',
    };
    if (score !== undefined) {
      feedbackInput.score = score;
    }
    const res = await recordFeedback(feedbackInput);
    const delta = signal === 'helpful' ? 1 : signal === 'harmful' ? -1 : -0.5;
    await updateCritic(claim_id, delta, 0, 5);

    await appendLog({
      id: `log_${reqId}`,
      op: 'feedback',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    return createToolResult({
      ...res,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'feedback',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('FEEDBACK_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
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
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション
    if (!id || !type || !name) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'id, type, name are required', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!isValidEntityType(type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `type must be one of: ${ENTITY_TYPES.join(', ')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // 文字列長バリデーション
    try {
      validateString('id', id, 256);
      validateString('name', name, 1024);
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      return createToolResult(
        { ...err('VALIDATION_ERROR', msg, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // Entity登録（exactOptionalPropertyTypes対応: undefinedを渡さない）
    const entity = await upsertEntity({
      id,
      type: type as 'Actor' | 'Artifact' | 'Event' | 'Concept',
      name,
      ...(canonical_key !== undefined && { canonical_key }),
      ...(attrs !== undefined && { attrs }),
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_entity',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      id: entity.id,
      type: entity.type,
      name: entity.name,
      canonical_key: entity.canonical_key,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_entity',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('UPSERT_ENTITY_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
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
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション
    if (!id || !src_id || !dst_id || !type) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'id, src_id, dst_id, type are required', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // 文字列長バリデーション
    try {
      validateString('id', id, 256);
      validateString('src_id', src_id, 256);
      validateString('dst_id', dst_id, 256);
      validateString('type', type, 256);
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      return createToolResult(
        { ...err('VALIDATION_ERROR', msg, reqId), trace_id: traceId },
        { isError: true }
      );
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

    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_relation',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      id: relation.id,
      src_id: relation.src_id,
      dst_id: relation.dst_id,
      type: relation.type,
      evidence_claim_id: relation.evidence_claim_id,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'upsert_relation',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('UPSERT_RELATION_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
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
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter =
      id !== undefined ||
      type !== undefined ||
      canonical_key !== undefined ||
      claim_id !== undefined;
    if (!hasFilter) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'at least one filter (id, type, canonical_key, claim_id) is required',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // typeのバリデーション
    if (type !== undefined && !isValidEntityType(type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `type must be one of: ${ENTITY_TYPES.join(', ')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // クエリ実行
    const filters: EntityQueryFilters = {
      ...(id !== undefined && { id }),
      ...(type !== undefined && { type: type as 'Actor' | 'Artifact' | 'Event' | 'Concept' }),
      ...(canonical_key !== undefined && { canonical_key }),
      ...(claim_id !== undefined && { claim_id }),
      ...(limit !== undefined && { limit }),
    };
    const entities = await queryEntities(filters);

    await appendLog({
      id: `log_${reqId}`,
      op: 'query_entity',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        entities,
        count: entities.length,
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'query_entity',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('QUERY_ENTITY_FAILED', msg, reqId), trace_id: traceId },
      { isError: true, useSafeStringify: true }
    );
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
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // バリデーション: 少なくとも1つのフィルターが必要
    const hasFilter =
      id !== undefined ||
      src_id !== undefined ||
      dst_id !== undefined ||
      type !== undefined ||
      evidence_claim_id !== undefined;
    if (!hasFilter) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'at least one filter (id, src_id, dst_id, type, evidence_claim_id) is required',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
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

    await appendLog({
      id: `log_${reqId}`,
      op: 'query_relation',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        relations,
        count: relations.length,
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'query_relation',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('QUERY_RELATION_FAILED', msg, reqId), trace_id: traceId },
      { isError: true, useSafeStringify: true }
    );
  }
}

export async function handleGetState(args: Record<string, unknown>) {
  const includeDetails = args?.['debug'] === true;
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  const summary = getStateSummary(includeDetails);
  const layerScopeSummary = includeDetails ? getLayerScopeSummary() : undefined;

  return createToolResult({
    ...summary,
    ...(layerScopeSummary ? { layer_scope: layerScopeSummary } : {}),
    request_id: reqId,
    trace_id: traceId,
  });
}

// ========== Sync Handlers (Issue #18) ==========

/**
 * Sync Push: ローカルDBから.pce-shared/へエクスポート
 */
export async function handleSyncPush(args: Record<string, unknown>) {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 引数の取得
    const {
      target_dir,
      scope_filter,
      boundary_filter,
      since,
      include_entities,
      include_relations,
    } = args as {
      target_dir?: string;
      scope_filter?: string[];
      boundary_filter?: string[];
      since?: string;
      include_entities?: boolean;
      include_relations?: boolean;
    };

    // Push実行オプションの構築
    const options: PushOptions = {
      basePath: process.cwd(),
      ...(target_dir && { targetDir: target_dir }),
      ...(scope_filter && { scopeFilter: scope_filter as Scope[] }),
      ...(boundary_filter && { boundaryFilter: boundary_filter as BoundaryClass[] }),
      ...(since && { since: new Date(since) }),
      ...(include_entities !== undefined && { includeEntities: include_entities }),
      ...(include_relations !== undefined && { includeRelations: include_relations }),
    };

    // Push実行
    const result = await executePush(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_push',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_PUSH_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_push',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      exported: result.right.exported,
      target_dir: result.right.targetDir,
      manifest_updated: result.right.manifestUpdated,
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_push',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_PUSH_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

/**
 * Sync Pull: .pce-shared/からローカルDBへインポート
 */
export async function handleSyncPull(args: Record<string, unknown>) {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 引数の取得
    const { source_dir, scope_filter, boundary_filter, dry_run } = args as {
      source_dir?: string;
      scope_filter?: string[];
      boundary_filter?: string[];
      dry_run?: boolean;
    };

    // Pull実行オプションの構築
    const options: PullOptions = {
      basePath: process.cwd(),
      ...(source_dir && { sourceDir: source_dir }),
      ...(scope_filter && { scopeFilter: scope_filter as Scope[] }),
      ...(boundary_filter && { boundaryFilter: boundary_filter as BoundaryClass[] }),
      ...(dry_run !== undefined && { dryRun: dry_run }),
    };

    // Pull実行
    const result = await executePull(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_pull',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_PULL_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 新しいClaimがインポートされた場合は状態遷移
    const totalNewClaims = result.right.imported.claims.new;

    if (totalNewClaims > 0 && !result.right.dryRun) {
      // totalNewClaims回分、状態遷移を行う（claimCountを増加させるため）
      for (let i = 0; i < totalNewClaims; i++) {
        transitionToHasClaims(true);
      }
    }

    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_pull',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      imported: {
        claims: {
          new: result.right.imported.claims.new,
          skipped_duplicate: result.right.imported.claims.skippedDuplicate,
          upgraded_boundary: result.right.imported.claims.upgradedBoundary,
        },
        entities: {
          new: result.right.imported.entities.new,
          skipped_duplicate: result.right.imported.entities.skippedDuplicate,
        },
        relations: {
          new: result.right.imported.relations.new,
          skipped_duplicate: result.right.imported.relations.skippedDuplicate,
        },
      },
      validation_errors: result.right.validationErrors,
      dry_run: result.right.dryRun,
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_pull',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_PULL_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

// ========== Tool Dispatcher ==========

/**
 * ツール名に基づいてハンドラをディスパッチ
 */
export async function dispatchTool(
  name: string,
  args: Record<string, unknown>
): Promise<ToolResult> {
  switch (name) {
    case 'pce.memory.policy.apply':
      return handlePolicyApply(args);
    case 'pce.memory.upsert':
      return handleUpsert(args);
    case 'pce.memory.upsert.entity':
      return handleUpsertEntity(args);
    case 'pce.memory.upsert.relation':
      return handleUpsertRelation(args);
    case 'pce.memory.query.entity':
      return handleQueryEntity(args);
    case 'pce.memory.query.relation':
      return handleQueryRelation(args);
    case 'pce.memory.activate':
      return handleActivate(args);
    case 'pce.memory.boundary.validate':
      return handleBoundaryValidate(args);
    case 'pce.memory.feedback':
      return handleFeedback(args);
    case 'pce.memory.state':
      return handleGetState(args);
    // Sync Tools (Issue #18)
    case 'pce.memory.sync.push':
      return handleSyncPush(args);
    case 'pce.memory.sync.pull':
      return handleSyncPull(args);
    default:
      return createToolResult(
        { error: { code: 'UNKNOWN_TOOL', message: `Unknown tool: ${name}` } },
        { isError: true }
      );
  }
}

// ========== Tool Definitions ==========

export const TOOL_DEFINITIONS = [
  {
    name: 'pce.memory.policy.apply',
    description: 'Apply policy (invariants, usage tags, redact rules)',
    inputSchema: {
      type: 'object',
      properties: {
        yaml: { type: 'string', description: 'Policy YAML (uses default if omitted)' },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.upsert',
    description: 'Register a claim (knowledge fragment). Provenance required',
    inputSchema: {
      type: 'object',
      properties: {
        text: { type: 'string' },
        kind: { type: 'string', enum: ['fact', 'preference', 'task', 'policy_hint'] },
        scope: { type: 'string', enum: ['session', 'project', 'principle'] },
        boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        content_hash: { type: 'string', pattern: '^sha256:[0-9a-f]{64}$' },
        provenance: {
          type: 'object',
          properties: {
            at: { type: 'string', format: 'date-time' },
            actor: { type: 'string' },
            git: {
              type: 'object',
              properties: {
                commit: { type: 'string' },
                repo: { type: 'string' },
                url: { type: 'string' },
                files: { type: 'array', items: { type: 'string' } },
              },
            },
            url: { type: 'string' },
            note: { type: 'string' },
            signed: { type: 'boolean' },
          },
          required: ['at'],
        },
        entities: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              type: { type: 'string', enum: ['Actor', 'Artifact', 'Event', 'Concept'] },
              name: { type: 'string' },
              canonical_key: { type: 'string' },
              attrs: { type: 'object' },
            },
            required: ['id', 'type', 'name'],
          },
        },
        relations: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              src_id: { type: 'string' },
              dst_id: { type: 'string' },
              type: { type: 'string' },
              props: { type: 'object' },
              evidence_claim_id: { type: 'string' },
            },
            required: ['id', 'src_id', 'dst_id', 'type'],
          },
        },
      },
      required: ['text', 'kind', 'scope', 'boundary_class', 'content_hash'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Claim ID' },
        is_new: { type: 'boolean', description: 'Whether this is a new claim' },
        graph_memory: {
          type: 'object',
          properties: {
            entities: {
              type: 'object',
              properties: {
                success: { type: 'integer', minimum: 0 },
                failed: { type: 'integer', minimum: 0 },
              },
              required: ['success', 'failed'],
            },
            relations: {
              type: 'object',
              properties: {
                success: { type: 'integer', minimum: 0 },
                failed: { type: 'integer', minimum: 0 },
              },
              required: ['success', 'failed'],
            },
          },
          description: 'Graph memory operation results (optional)',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'is_new', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.activate',
    description: 'Build active context (AC) based on query and policy',
    inputSchema: {
      type: 'object',
      properties: {
        scope: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
        },
        allow: { type: 'array', items: { type: 'string' } },
        top_k: { type: 'integer', minimum: 1, maximum: 50 },
        q: { type: 'string', description: 'Search query string (partial match)' },
        cursor: { type: 'string', description: 'Pagination cursor' },
        include_meta: {
          type: 'boolean',
          description: 'Include metadata (evidence, etc.)',
          default: false,
        },
      },
      required: ['scope', 'allow'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        active_context_id: { type: 'string', description: 'Active context ID' },
        claims: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              claim: { type: 'object', description: 'Claim data' },
              score: { type: 'number', description: 'Relevance score' },
              evidences: { type: 'array', items: { type: 'object' }, description: 'Evidence list' },
            },
          },
          description: 'Scored claims with optional evidences',
        },
        claims_count: { type: 'integer', minimum: 0, description: 'Number of claims returned' },
        next_cursor: { type: 'string', description: 'Pagination cursor for next page' },
        has_more: { type: 'boolean', description: 'Whether more results exist' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: [
        'active_context_id',
        'claims',
        'claims_count',
        'has_more',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce.memory.boundary.validate',
    description: 'Pre-generation boundary check / Redact-before-Send',
    inputSchema: {
      type: 'object',
      properties: {
        payload: { type: 'string' },
        allow: { type: 'array', items: { type: 'string' } },
        scope: { type: 'string', enum: ['session', 'project', 'principle'] },
      },
      required: ['payload'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        allowed: { type: 'boolean', description: 'Whether the payload is allowed' },
        redacted: { type: 'string', description: 'Redacted payload' },
        violations: {
          type: 'array',
          items: { type: 'string' },
          description: 'List of boundary violations',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['allowed', 'redacted', 'policy_version', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.feedback',
    description: 'Update critic with signal (helpful/harmful/outdated/duplicate)',
    inputSchema: {
      type: 'object',
      properties: {
        claim_id: { type: 'string' },
        signal: { type: 'string', enum: ['helpful', 'harmful', 'outdated', 'duplicate'] },
        score: { type: 'number', minimum: -1, maximum: 1 },
      },
      required: ['claim_id', 'signal'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Feedback ID' },
        claim_id: { type: 'string', description: 'Target claim ID' },
        signal: {
          type: 'string',
          enum: ['helpful', 'harmful', 'outdated', 'duplicate'],
          description: 'Feedback signal',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'claim_id', 'signal', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.state',
    description: 'Get current state machine status (Uninitialized/PolicyApplied/HasClaims/Ready)',
    inputSchema: {
      type: 'object',
      properties: {
        debug: {
          type: 'boolean',
          description: 'Debug mode: include runtime_state details (default: false)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        claim_count: { type: 'integer', minimum: 0, description: 'Number of claims' },
        active_context_id: { type: 'string', description: 'Current active context ID' },
        runtime_state: { type: 'object', description: 'Runtime state details (debug mode)' },
        layer_scope: { type: 'object', description: 'Layer/scope state (debug mode)' },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['state', 'policy_version', 'request_id', 'trace_id'],
    },
  },
  // ========== Graph Memory Tools ==========
  {
    name: 'pce.memory.upsert.entity',
    description: 'Register an entity in graph memory (Actor/Artifact/Event/Concept)',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        name: { type: 'string', description: 'Entity name' },
        canonical_key: {
          type: 'string',
          description: 'Canonical key (optional, for deduplication)',
        },
        attrs: { type: 'object', description: 'Additional attributes (optional)' },
      },
      required: ['id', 'type', 'name'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        name: { type: 'string', description: 'Entity name' },
        canonical_key: { type: 'string', description: 'Canonical key (if set)' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'type', 'name', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.upsert.relation',
    description: 'Register a relation between entities in graph memory',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type (e.g., KNOWS, USES, DEPENDS_ON)' },
        props: { type: 'object', description: 'Additional relation properties (optional)' },
        evidence_claim_id: {
          type: 'string',
          description: 'Claim ID as evidence for this relation (optional)',
        },
      },
      required: ['id', 'src_id', 'dst_id', 'type'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type' },
        evidence_claim_id: { type: 'string', description: 'Evidence claim ID (if set)' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: [
        'id',
        'src_id',
        'dst_id',
        'type',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce.memory.query.entity',
    description: 'Query entities from graph memory by ID, type, canonical_key, or claim_id',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID (exact match)' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        canonical_key: { type: 'string', description: 'Canonical key (exact match)' },
        claim_id: { type: 'string', description: 'Claim ID to find linked entities' },
        limit: {
          type: 'integer',
          minimum: 1,
          maximum: 100,
          description: 'Max results (default: 50)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        entities: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              type: { type: 'string', enum: ['Actor', 'Artifact', 'Event', 'Concept'] },
              name: { type: 'string' },
              canonical_key: { type: 'string' },
              attrs: { type: 'object' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'type', 'name'],
          },
          description: 'Matching entities',
        },
        count: { type: 'integer', minimum: 0, description: 'Number of entities returned' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['entities', 'count', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce.memory.query.relation',
    description:
      'Query relations from graph memory by ID, src_id, dst_id, type, or evidence_claim_id',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID (exact match)' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type (e.g., TAGGED, KNOWS)' },
        evidence_claim_id: { type: 'string', description: 'Evidence claim ID' },
        limit: {
          type: 'integer',
          minimum: 1,
          maximum: 100,
          description: 'Max results (default: 50)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        relations: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              src_id: { type: 'string' },
              dst_id: { type: 'string' },
              type: { type: 'string' },
              evidence_claim_id: { type: 'string' },
              props: { type: 'object' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'src_id', 'dst_id', 'type'],
          },
          description: 'Matching relations',
        },
        count: { type: 'integer', minimum: 0, description: 'Number of relations returned' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['relations', 'count', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  // ========== Sync Tools (Issue #18) ==========
  {
    name: 'pce.memory.sync.push',
    description:
      'Export local claims/entities/relations to .pce-shared/ directory for Git-based CRDT sync',
    inputSchema: {
      type: 'object',
      properties: {
        target_dir: {
          type: 'string',
          description: 'Target directory path (default: .pce-shared)',
        },
        scope_filter: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Filter by scope (default: ["project", "principle"])',
        },
        boundary_filter: {
          type: 'array',
          items: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
          description:
            'Filter by boundary_class (default: ["public", "internal"], secret is always excluded)',
        },
        since: {
          type: 'string',
          format: 'date-time',
          description: 'Export only claims created/updated after this time (ISO8601)',
        },
        include_entities: {
          type: 'boolean',
          description: 'Include entities in export (default: true)',
        },
        include_relations: {
          type: 'boolean',
          description: 'Include relations in export (default: true)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        exported: {
          type: 'object',
          properties: {
            claims: { type: 'integer', minimum: 0 },
            entities: { type: 'integer', minimum: 0 },
            relations: { type: 'integer', minimum: 0 },
          },
          required: ['claims', 'entities', 'relations'],
        },
        target_dir: { type: 'string', description: 'Actual target directory path' },
        manifest_updated: { type: 'boolean', description: 'Whether manifest.json was updated' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'exported',
        'target_dir',
        'manifest_updated',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce.memory.sync.pull',
    description:
      'Import claims/entities/relations from .pce-shared/ directory with CRDT merge strategy',
    inputSchema: {
      type: 'object',
      properties: {
        source_dir: {
          type: 'string',
          description: 'Source directory path (default: .pce-shared)',
        },
        scope_filter: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Filter by scope (default: all)',
        },
        boundary_filter: {
          type: 'array',
          items: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
          description: 'Filter by boundary_class (default: all except secret)',
        },
        dry_run: {
          type: 'boolean',
          description: 'Preview changes without applying (default: false)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        imported: {
          type: 'object',
          properties: {
            claims: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
                upgraded_boundary: { type: 'integer', minimum: 0 },
              },
              required: ['new', 'skipped_duplicate', 'upgraded_boundary'],
            },
            entities: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
              },
              required: ['new', 'skipped_duplicate'],
            },
            relations: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
              },
              required: ['new', 'skipped_duplicate'],
            },
          },
          required: ['claims', 'entities', 'relations'],
        },
        validation_errors: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              error: { type: 'string' },
            },
            required: ['file', 'error'],
          },
          description: 'List of validation errors encountered',
        },
        dry_run: { type: 'boolean', description: 'Whether this was a dry run' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'imported',
        'validation_errors',
        'dry_run',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
];

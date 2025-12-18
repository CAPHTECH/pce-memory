/**
 * MCP Tool Handlers（コア実装）
 *
 * デーモンモード/stdioモード両方から利用可能なハンドラ実装。
 * index.tsから抽出し、再利用可能にした。
 */

import { boundaryValidate, allowTagMatches as boundaryAllowTagMatches } from '@pce/boundary';
import { computeContentHash } from '@pce/embeddings';
import { upsertClaim, upsertClaimWithEmbedding, findClaimById } from '../store/claims.js';
import type { Provenance } from '../store/claims.js';
import { hybridSearchPaginated, getEmbeddingService } from '../store/hybridSearch.js';
import { upsertEntity, linkClaimEntity, queryEntities } from '../store/entities.js';
import type { EntityInput, EntityQueryFilters } from '../store/entities.js';
import { upsertRelation, queryRelations } from '../store/relations.js';
import type { RelationInput, RelationQueryFilters } from '../store/relations.js';
import { getEvidenceForClaims, insertEvidence } from '../store/evidence.js';
import type { Evidence } from '../store/evidence.js';
import {
  gcExpiredObservations,
  insertObservation,
  type InsertObservationInput,
  type ObservationSourceType,
} from '../store/observations.js';
import { analyzeTextSensitivity, redactPiiText } from '../audit/redactText.js';
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
  executeStatus,
  type PushOptions,
  type PullOptions,
  type StatusOptions,
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

// Issue #30 Review: allowTagMatchesを@pce/boundaryからインポートして重複排除
// 後方互換性のためローカルエイリアスを維持
const allowTagMatches = boundaryAllowTagMatches;

function isAllowedByBoundary(allowList: string[], requestedAllow: string[]): boolean {
  return allowList.some((p) => requestedAllow.some((t) => allowTagMatches(p, t)));
}

// ========== Upsert Helper Functions ==========

/**
 * Upsertの入力バリデーション
 * 状態検証、レート制限、フィールド検証を実行
 */
interface UpsertValidationResult {
  isValid: boolean;
  errorResponse?: ToolResult;
  resolvedHash?: string; // Auto-generated or validated content_hash
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

  if (!text || !kind || !scope || !boundary_class) {
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

  // content_hash処理: 未指定時は自動生成、指定時は検証
  const computedHash = `sha256:${computeContentHash(text)}`;
  let resolvedHash: string;

  if (content_hash) {
    // 指定時: 一致検証（改竄防止）
    if (content_hash !== computedHash) {
      return {
        isValid: false,
        errorResponse: createToolResult(
          {
            ...err(
              'VALIDATION_ERROR',
              'content_hash mismatch: provided hash does not match computed hash for text',
              reqId
            ),
            trace_id: traceId,
          },
          { isError: true }
        ),
      };
    }
    resolvedHash = content_hash;
  } else {
    // 未指定時: 自動生成
    resolvedHash = computedHash;
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

  return { isValid: true, resolvedHash };
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

    // Defensive guard for resolvedHash (should never happen if isValid is true)
    if (!validation.resolvedHash) {
      return createToolResult(
        {
          ...err('STATE_ERROR', 'resolvedHash missing after validation', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    // Claim登録（EmbeddingServiceがあれば埋め込みも生成）
    const claimInput = {
      text: text!,
      kind: kind!,
      scope: scope!,
      boundary_class: boundary_class!,
      content_hash: validation.resolvedHash,
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
      content_hash: validation.resolvedHash,
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

export async function handleObserve(args: Record<string, unknown>) {
  const {
    source_type,
    source_id,
    content,
    actor,
    tags,
    provenance,
    ttl_days,
    extract,
    boundary_class,
  } = args as {
    source_type?: unknown;
    source_id?: unknown;
    content?: unknown;
    actor?: unknown;
    tags?: unknown;
    provenance?: Provenance;
    ttl_days?: unknown;
    extract?: unknown;
    boundary_class?: unknown;
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
    if (!canDoUpsert()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!isInActiveScope(scopeId)) {
      return createToolResult(
        { ...err('STATE_ERROR', 'scope not active', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (typeof source_type !== 'string') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'source_type is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const allowedSourceTypes: ObservationSourceType[] = ['chat', 'tool', 'file', 'http', 'system'];
    if (!allowedSourceTypes.includes(source_type as ObservationSourceType)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'invalid source_type', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (typeof content !== 'string' || content.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'content is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // サイズ制限（将来的にはpolicy/envで調整）
    try {
      if (source_id !== undefined) validateString('source_id', source_id, 2_048);
      if (actor !== undefined) validateString('actor', actor, 512);
    } catch (e) {
      const msg = e instanceof Error ? e.message : String(e);
      return createToolResult(
        { ...err('VALIDATION_ERROR', msg, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    let tagsList: string[] | undefined;
    if (tags !== undefined) {
      if (!Array.isArray(tags) || tags.some((t) => typeof t !== 'string')) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'tags must be string[]', reqId), trace_id: traceId },
          { isError: true }
        );
      }
      tagsList = tags as string[];
      if (tagsList.length > 32) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'too many tags', reqId), trace_id: traceId },
          { isError: true }
        );
      }
      // Issue #30 Review: 各タグの長さとパターンを検証（JSONインジェクション/DB肥大化防止）
      const TAG_MAX_LENGTH = 256;
      const TAG_PATTERN = /^[\w\-:.@/]+$/; // 安全な文字セット（英数字、ハイフン、コロン、ドット、アット、スラッシュ）
      for (const tag of tagsList) {
        if (tag.length > TAG_MAX_LENGTH) {
          return createToolResult(
            {
              ...err('VALIDATION_ERROR', `tag too long (max ${TAG_MAX_LENGTH})`, reqId),
              trace_id: traceId,
            },
            { isError: true }
          );
        }
        if (!TAG_PATTERN.test(tag)) {
          return createToolResult(
            {
              ...err('VALIDATION_ERROR', 'tag contains invalid characters', reqId),
              trace_id: traceId,
            },
            { isError: true }
          );
        }
      }
    }

    // ttl_days（default + clamp）
    const defaultTtlDaysRaw = Number(process.env['PCE_OBS_TTL_DAYS'] ?? '30');
    const defaultTtlDays =
      Number.isFinite(defaultTtlDaysRaw) && defaultTtlDaysRaw > 0 ? defaultTtlDaysRaw : 30;
    const maxTtlDaysRaw = Number(process.env['PCE_OBS_TTL_DAYS_MAX'] ?? '90');
    const maxTtlDays = Number.isFinite(maxTtlDaysRaw) && maxTtlDaysRaw > 0 ? maxTtlDaysRaw : 90;

    const requestedTtl =
      typeof ttl_days === 'number'
        ? ttl_days
        : typeof ttl_days === 'string'
          ? Number(ttl_days)
          : undefined;
    if (requestedTtl !== undefined && (!Number.isFinite(requestedTtl) || requestedTtl < 1)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'ttl_days must be a positive number', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    const ttlDays = Math.min(requestedTtl ?? defaultTtlDays, maxTtlDays);

    const extractMode =
      typeof extract === 'object' && extract !== null && 'mode' in extract
        ? (extract as { mode?: unknown }).mode
        : undefined;
    const mode = (extractMode ?? 'noop') as 'noop' | 'single_claim_v0';
    if (mode !== 'noop' && mode !== 'single_claim_v0') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'invalid extract.mode', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // provenanceは任意。ただし存在する場合は at が必須
    if (provenance !== undefined) {
      if (
        typeof provenance !== 'object' ||
        provenance === null ||
        typeof provenance.at !== 'string'
      ) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'provenance.at is required', reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    // ========== Observation Security（best-effort / fail-safe） ==========
    const warnings: string[] = [];

    const policy = getPolicy();
    const allowedBoundaryClasses = ['public', 'internal', 'pii', 'secret'] as const;
    type BoundaryClassInput = (typeof allowedBoundaryClasses)[number];

    const requestedBoundaryClass: BoundaryClassInput | null = (() => {
      if (boundary_class === undefined) return 'internal';
      if (typeof boundary_class !== 'string') return null;
      if (!allowedBoundaryClasses.includes(boundary_class as BoundaryClassInput)) return null;
      return boundary_class as BoundaryClassInput;
    })();
    if (requestedBoundaryClass === null) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'boundary_class must be one of public|internal|pii|secret',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (!policy.boundary_classes[requestedBoundaryClass]) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown boundary_class', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    const maxBytesRaw = Number(process.env['PCE_OBS_MAX_BYTES'] ?? '65536');
    const maxBytes = Number.isFinite(maxBytesRaw) && maxBytesRaw > 0 ? maxBytesRaw : 65_536;
    const contentBytes = Buffer.byteLength(content, 'utf8');
    if (contentBytes > maxBytes) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'content too large', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    const sensitivity = analyzeTextSensitivity(content);
    const piiRedaction = redactPiiText(content);
    const detectedBoundaryClass: BoundaryClassInput =
      sensitivity.secret.length > 0
        ? 'secret'
        : sensitivity.pii.length > 0 || piiRedaction.hits.length > 0
          ? 'pii'
          : requestedBoundaryClass;

    const severity: Record<BoundaryClassInput, number> = {
      public: 0,
      internal: 1,
      pii: 2,
      secret: 3,
    };
    const effectiveBoundaryClass: BoundaryClassInput =
      severity[detectedBoundaryClass] > severity[requestedBoundaryClass]
        ? detectedBoundaryClass
        : requestedBoundaryClass;

    type ObsStoreMode = 'raw' | 'redact' | 'digest_only';
    const storeModeRaw = String(process.env['PCE_OBS_STORE_MODE'] ?? 'redact').toLowerCase();
    const envStoreMode: ObsStoreMode =
      storeModeRaw === 'raw' || storeModeRaw === 'digest_only' || storeModeRaw === 'redact'
        ? (storeModeRaw as ObsStoreMode)
        : 'redact';

    const modeByBoundary: ObsStoreMode =
      effectiveBoundaryClass === 'secret'
        ? 'digest_only'
        : effectiveBoundaryClass === 'pii'
          ? 'redact'
          : envStoreMode;

    const effectiveStoreMode: ObsStoreMode =
      process.env['NODE_ENV'] === 'production' && modeByBoundary === 'raw'
        ? 'redact'
        : modeByBoundary;

    const contentToStore: string | null =
      effectiveStoreMode === 'digest_only'
        ? null
        : effectiveStoreMode === 'redact'
          ? piiRedaction.redacted
          : content;
    const contentWasRedacted = contentToStore !== null && contentToStore !== content;

    if (effectiveStoreMode !== 'raw' && sensitivity.secret.length > 0) {
      warnings.push('OBS_CONTENT_NOT_STORED_SECRET');
    }
    if (contentWasRedacted) {
      warnings.push('OBS_CONTENT_REDACTED');
    }

    // 期限切れObservationをGC（ベストエフォート）
    try {
      await gcExpiredObservations('scrub');
    } catch {
      // GC失敗はobserve本体を止めない（監査ログに頼る）
    }

    const observationId = `obs_${crypto.randomUUID().slice(0, 8)}`;
    // Issue #30 Review: secretの場合はdigestも保存しない（短いシークレットのハッシュから推測されるリスク）
    // 代わりに固定のプレースホルダを使用
    const contentDigest =
      effectiveBoundaryClass === 'secret'
        ? 'sha256:REDACTED_SECRET'
        : `sha256:${computeContentHash(content)}`;
    const contentLength = contentBytes;
    const expiresAt = new Date(Date.now() + ttlDays * 86_400_000).toISOString();

    const observationInput: InsertObservationInput = {
      id: observationId,
      source_type: source_type as ObservationSourceType,
      content: contentToStore,
      content_digest: contentDigest,
      content_length: contentLength,
      expires_at: expiresAt,
    };
    // exactOptionalPropertyTypes対応: undefinedを明示的に渡さない
    if (typeof source_id === 'string') observationInput.source_id = source_id;
    if (typeof actor === 'string') observationInput.actor = actor;
    if (tagsList !== undefined) observationInput.tags = tagsList;
    await insertObservation(observationInput);

    const claimIds: string[] = [];
    const effectiveExtractMode =
      mode === 'single_claim_v0' && effectiveBoundaryClass === 'secret' ? 'noop' : mode;
    if (mode === 'single_claim_v0' && effectiveExtractMode === 'noop') {
      warnings.push('EXTRACT_SKIPPED_SECRET');
    }

    if (effectiveExtractMode === 'single_claim_v0') {
      // 暫定: Observation.contentをそのまま1Claim化（配線確認用）
      if (effectiveBoundaryClass === 'secret') {
        // 防御的（ここには来ない想定）
        return createToolResult(
          {
            ...err('VALIDATION_ERROR', 'secret content cannot be extracted', reqId),
            trace_id: traceId,
          },
          { isError: true }
        );
      }

      const claimText = effectiveBoundaryClass === 'pii' ? piiRedaction.redacted : content;
      const claimHash = `sha256:${computeContentHash(claimText)}`;

      const claimInput = {
        text: claimText,
        kind: 'fact',
        scope: 'session',
        boundary_class: effectiveBoundaryClass,
        content_hash: claimHash,
        ...(provenance !== undefined ? { provenance } : {}),
      };

      const embeddingService = getEmbeddingService();
      const { claim, isNew } = embeddingService
        ? await upsertClaimWithEmbedding(claimInput, embeddingService)
        : await upsertClaim(claimInput);

      // スコープへのリソース登録（claimのみ）
      const addResult = addResourceToCurrentScope(scopeId, claim.id);
      if (E.isLeft(addResult)) {
        console.error(`[Handler] Failed to add resource to scope: ${addResult.left.message}`);
      }

      transitionToHasClaims(isNew);
      claimIds.push(claim.id);

      // Evidence: Claimの根拠としてObservationを記録（長期保持は最小限に寄せる）
      const safeSnippet = `${contentDigest} bytes=${contentLength}`;
      await insertEvidence({
        id: `evd_${crypto.randomUUID().slice(0, 8)}`,
        claim_id: claim.id,
        source_type: 'observation',
        source_id: observationId,
        snippet: safeSnippet,
        at: provenance?.at ?? new Date().toISOString(),
      });
    }

    await appendLog({
      id: `log_${reqId}`,
      op: 'observe',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      observation_id: observationId,
      claim_ids: claimIds,
      effective_boundary_class: effectiveBoundaryClass,
      content_stored: contentToStore !== null,
      content_redacted: contentWasRedacted,
      ...(warnings.length > 0 ? { warnings } : {}),
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'observe',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('DB_ERROR', msg, reqId), trace_id: traceId },
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
    const policy = getPolicy();
    const allowTags = allow as string[];
    const allowedResults = searchResult.results.filter((r) => {
      const bc = policy.boundary_classes[r.claim.boundary_class];
      if (!bc) return false;
      return isAllowedByBoundary(bc.allow ?? [], allowTags);
    });

    const claims = allowedResults.map((r) => r.claim);
    const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
    await saveActiveContext({ id: acId, claims });

    let evidenceMap: Map<string, Evidence[]> | undefined;
    if (include_meta && claims.length > 0) {
      const claimIds = claims.map((c) => c.id);
      evidenceMap = await getEvidenceForClaims(claimIds);
    }

    const scoredItems = allowedResults.map((r) => ({
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
    const { source_dir, scope_filter, boundary_filter, dry_run, since } = args as {
      source_dir?: string;
      scope_filter?: string[];
      boundary_filter?: string[];
      dry_run?: boolean;
      since?: string; // Phase 2: 増分インポート用ISO8601日時
    };

    // Pull実行オプションの構築
    const options: PullOptions = {
      basePath: process.cwd(),
      ...(source_dir && { sourceDir: source_dir }),
      ...(scope_filter && { scopeFilter: scope_filter as Scope[] }),
      ...(boundary_filter && { boundaryFilter: boundary_filter as BoundaryClass[] }),
      ...(dry_run !== undefined && { dryRun: dry_run }),
      ...(since && { since: new Date(since) }), // Phase 2: since追加
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
          skipped_by_since: result.right.imported.claims.skippedBySince, // Phase 2
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
      manifest_updated: result.right.manifestUpdated, // Phase 2
      // Phase 3: 衝突検出レポート
      conflicts: {
        total: result.right.conflicts.conflicts.length,
        auto_resolved: result.right.conflicts.autoResolved,
        skipped: result.right.conflicts.skipped,
        details: result.right.conflicts.conflicts.slice(0, 10), // 最初の10件のみ
      },
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

/**
 * Sync Status Handler (Phase 2)
 * 同期ディレクトリの状態を確認
 */
export async function handleSyncStatus(args: Record<string, unknown>) {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以上で実行可能）
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

    // 引数の取得と検証
    const { target_dir } = args as { target_dir?: unknown };

    // 型検証: target_dirはstring | undefinedのみ許可
    if (target_dir !== undefined && typeof target_dir !== 'string') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'target_dir must be a string', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // Statusオプション構築
    const options: StatusOptions = {
      basePath: process.cwd(),
      ...(typeof target_dir === 'string' && { targetDir: target_dir }),
    };

    // Status実行
    const result = await executeStatus(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_status',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_STATUS_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 成功時のログ記録
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_status',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      exists: result.right.exists,
      manifest: result.right.manifest,
      files: result.right.files,
      validation: result.right.validation,
      target_dir: result.right.targetDir,
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_status',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_STATUS_FAILED', msg, reqId), trace_id: traceId },
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
    case 'pce.memory.observe':
      return handleObserve(args);
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
    case 'pce.memory.sync.status':
      return handleSyncStatus(args);
    default:
      return createToolResult(
        { error: { code: 'UNKNOWN_TOOL', message: `Unknown tool: ${name}` } },
        { isError: true }
      );
  }
}

// ========== MCP Prompts (Issue #16) ==========

/**
 * Prompt定義型
 */
export interface PromptDefinition {
  name: string;
  description?: string;
  arguments?: Array<{
    name: string;
    description?: string;
    required?: boolean;
  }>;
}

/**
 * Promptメッセージ型
 */
export interface PromptMessage {
  role: 'user' | 'assistant';
  content: {
    type: 'text';
    text: string;
  };
}

/**
 * 定義済みPrompts一覧
 */
export const PROMPTS_DEFINITIONS: PromptDefinition[] = [
  {
    name: 'recall_context',
    description: 'Guide for recalling relevant knowledge before starting a task',
    arguments: [
      {
        name: 'query',
        description: 'Search query (e.g., "authentication", "API design")',
        required: false,
      },
      {
        name: 'scope',
        description: 'Scope (session/project/principle)',
        required: false,
      },
    ],
  },
  {
    name: 'record_decision',
    description: 'Guide for recording design decisions',
    arguments: [
      {
        name: 'topic',
        description: 'Decision topic (e.g., "state management library selection")',
        required: true,
      },
    ],
  },
  {
    name: 'sync_workflow',
    description: 'Guide for Git sync workflow (push/pull/status)',
    arguments: [
      {
        name: 'operation',
        description: 'Operation type (push/pull/status)',
        required: false,
      },
    ],
  },
  {
    name: 'sync_push',
    description: 'Guide for exporting local knowledge to .pce-shared/ directory',
    arguments: [
      {
        name: 'scope_filter',
        description: 'Filter by scope (e.g., "project,principle")',
        required: false,
      },
      {
        name: 'boundary_filter',
        description: 'Filter by boundary class (e.g., "public,internal")',
        required: false,
      },
    ],
  },
  {
    name: 'sync_pull',
    description: 'Guide for importing shared knowledge from .pce-shared/ directory',
    arguments: [
      {
        name: 'dry_run',
        description: 'Preview changes without applying (true/false)',
        required: false,
      },
      {
        name: 'since',
        description: 'Incremental import from date (ISO8601)',
        required: false,
      },
    ],
  },
  {
    name: 'debug_assist',
    description: 'Guide for searching related knowledge during debugging',
    arguments: [
      {
        name: 'error_message',
        description: 'Error message or keyword',
        required: false,
      },
    ],
  },
];

/**
 * Generate prompt messages
 */
function generatePromptMessages(
  prompt: PromptDefinition,
  args?: Record<string, string>
): PromptMessage[] {
  switch (prompt.name) {
    case 'recall_context': {
      const query = args?.['query'] || '<keyword to search>';
      const scope = args?.['scope'] || 'project';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Before starting a task, I want to recall relevant knowledge. Search query: "${query}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce.memory.activate to recall relevant knowledge.

\`\`\`json
{
  "q": "${query}",
  "scope": ["${scope}"],
  "allow": ["answer:*"],
  "top_k": 10
}
\`\`\`

## Usage Tips

1. **Scope Selection**:
   - \`session\`: Information limited to current conversation
   - \`project\`: Project-specific patterns and conventions
   - \`principle\`: Universal principles (SOLID, TDD, etc.)

2. **Query Tips**:
   - Use space-separated keywords (OR search)
   - Use specific keywords ("JWT authentication" rather than "auth")

3. **Post-recall Actions**:
   - Send \`helpful\` feedback for useful knowledge
   - Send \`outdated\` for stale information`,
          },
        },
      ];
    }

    case 'record_decision': {
      const topic = args?.['topic'] || '<decision topic>';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to record a design decision. Topic: "${topic}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce.memory.upsert to record the design decision.

\`\`\`json
{
  "text": "Decision on ${topic}: <describe the decision>",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "content_hash": "sha256:<SHA256 hash of text>",
  "provenance": {
    "at": "<current ISO8601 datetime>",
    "actor": "claude",
    "note": "ADR-XXXX / Issue #YYY"
  }
}
\`\`\`

## Recording Guidelines

1. **Kind Selection**:
   - \`fact\`: Architecture decisions, technical constraints
   - \`preference\`: Coding styles, tool choices
   - \`task\`: Work in progress, TODOs
   - \`policy_hint\`: Security requirements, operational rules

2. **Boundary Class**:
   - \`public\`: Publicly shareable information
   - \`internal\`: Internal use only
   - \`pii\`: Contains personal information
   - \`secret\`: Credentials (not recommended to store)

3. **Provenance**:
   - \`at\`: Required. Recording timestamp
   - \`actor\`: Recorder (claude/user)
   - \`note\`: Reference to ADR number or Issue number`,
          },
        },
      ];
    }

    case 'sync_workflow': {
      const operation = args?.['operation'] || 'status';
      const operationGuides: Record<string, string> = {
        push: `## Push: Export Local Knowledge

Use pce.memory.sync.push to export knowledge from the local DB to .pce-shared/.

\`\`\`json
{
  "scope_filter": ["project", "principle"],
  "boundary_filter": ["public", "internal"]
}
\`\`\`

### Options
- \`target_dir\`: Export destination (default: .pce-shared at Git root if available)
- \`scope_filter\`: Filter by scope
- \`boundary_filter\`: Filter by boundary_class (secret is always excluded)
- \`since\`: Export only changes after the specified datetime

### Notes
- Information with secret boundary is automatically excluded
- pii is only included when explicitly specified`,

        pull: `## Pull: Import Shared Knowledge

Use pce.memory.sync.pull to import knowledge from .pce-shared/.

\`\`\`json
{
  "dry_run": true
}
\`\`\`

### Options
- \`source_dir\`: Import source (default: .pce-shared at Git root if available)
- \`scope_filter\`: Filter by scope
- \`boundary_filter\`: Filter by boundary_class
- \`dry_run\`: Preview changes without applying when true
- \`since\`: Incremental import (only after the specified datetime)

### CRDT Merge Strategy
- Claims with same content_hash are skipped as duplicates
- boundary_class can only be upgraded (public→internal), not downgraded
- Conflicts are auto-resolved (boundary_upgrade) or skipped`,

        status: `## Status: Check Sync State

Use pce.memory.sync.status to check the state of the sync directory.

\`\`\`json
{}
\`\`\`

### Available Information
- \`exists\`: Directory existence
- \`manifest\`: Version, last push/pull timestamps
- \`files\`: File counts for claims/entities/relations
- \`validation\`: JSON schema validation results`,
      };

      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Tell me how to use Git sync functionality. Operation: ${operation}`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text:
              operationGuides[operation] ||
              `# Git-based CRDT Sync

pce-memory allows synchronizing knowledge across teams via Git.

## Basic Workflow

1. **status** - Check current sync state
2. **pull** - Import shared knowledge (dry_run: true for preview)
3. **work** - Record and update knowledge
4. **push** - Export local knowledge
5. **git commit/push** - Share changes via Git

## CLI Commands

\`\`\`bash
pce-memory sync status
pce-memory sync pull --dry-run
pce-memory sync push
\`\`\`

## Git Hooks Integration

Automatic sync with pre-commit and post-merge hooks:
\`\`\`bash
./scripts/git-hooks/install-hooks.sh
export PCE_SYNC_ENABLED=true
\`\`\``,
          },
        },
      ];
    }

    case 'sync_push': {
      const scopeFilter = args?.['scope_filter'] || 'project,principle';
      const boundaryFilter = args?.['boundary_filter'] || 'public,internal';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to export local knowledge to share with the team.`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce.memory.sync.push to export knowledge to .pce-shared/ directory.

\`\`\`json
{
  "scope_filter": ["${scopeFilter.split(',').join('", "')}"],
  "boundary_filter": ["${boundaryFilter.split(',').join('", "')}"],
  "include_entities": true,
  "include_relations": true
}
\`\`\`

## Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| \`target_dir\` | .pce-shared | Export destination directory |
| \`scope_filter\` | project, principle | Filter by scope (session excluded by default) |
| \`boundary_filter\` | public, internal | Filter by boundary class |
| \`since\` | - | Export only claims updated after this ISO8601 datetime |
| \`include_entities\` | true | Include graph entities in export |
| \`include_relations\` | true | Include graph relations in export |

## Security Notes

- \`secret\` boundary is **always excluded** from export
- \`pii\` is only included when explicitly specified in boundary_filter
- Review exported files before committing to Git

## After Push

\`\`\`bash
# Stage the exported files
git add .pce-shared/

# Commit and push
git commit -m "chore: update shared knowledge"
git push
\`\`\``,
          },
        },
      ];
    }

    case 'sync_pull': {
      const since = args?.['since'] || '';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to import shared knowledge from the team.`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce.memory.sync.pull to import knowledge from .pce-shared/ directory.

## Step 1: Preview Changes (Recommended)

\`\`\`json
{
  "dry_run": true
}
\`\`\`

## Step 2: Apply Changes

\`\`\`json
{
  "dry_run": false${since ? `,\n  "since": "${since}"` : ''}
}
\`\`\`

## Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| \`source_dir\` | .pce-shared | Import source directory |
| \`scope_filter\` | all | Filter by scope |
| \`boundary_filter\` | all except secret | Filter by boundary class |
| \`dry_run\` | false | Preview without applying changes |
| \`since\` | - | Incremental import from ISO8601 datetime |

## CRDT Merge Behavior

| Scenario | Behavior |
|----------|----------|
| Same content_hash exists | Skip (duplicate) |
| boundary_class differs | Upgrade only (public→internal) |
| Entity/relation conflict | Skip with warning |

## Best Practices

1. **Always dry_run first**: Preview changes before applying
2. **Use incremental import**: Specify \`since\` for large knowledge bases
3. **Review conflicts**: Check skipped items in the result
4. **Pull before push**: Avoid overwriting team's changes`,
          },
        },
      ];
    }

    case 'debug_assist': {
      const errorMessage = args?.['error_message'] || '<error message>';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `An error occurred during debugging: "${errorMessage}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce.memory.activate to search for past similar issues and solutions.

\`\`\`json
{
  "q": "${errorMessage}",
  "scope": ["project", "session"],
  "allow": ["answer:*"],
  "top_k": 15
}
\`\`\`

## Leveraging Knowledge During Debugging

1. **Search by error message**: Check if there's a record of solving the same error before
2. **Search by related component**: Check known issues for the module where the error occurred
3. **Record after resolution**: Use \`upsert\` to record new solutions

## Query Tips

- Include error codes (e.g., "ECONNREFUSED", "TypeError")
- Include library names (e.g., "DuckDB lock")
- Include symptoms (e.g., "timeout", "memory leak")

## Example of Recording a Solution

\`\`\`json
{
  "text": "DuckDB 'Could not set lock on file' error: Need to explicitly close socket with server.close()",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal"
}
\`\`\``,
          },
        },
      ];
    }

    default:
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Tell me about ${prompt.name}`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: prompt.description || 'No description available for this prompt.',
          },
        },
      ];
  }
}

/**
 * prompts/list ハンドラ
 */
export async function handleListPrompts(args: Record<string, unknown>): Promise<{
  prompts: PromptDefinition[];
}> {
  const { cursor } = args as { cursor?: string };

  // ページネーション処理
  const PAGE_SIZE = 10;
  const startIdx = cursor ? parseInt(cursor, 10) : 0;
  const prompts = PROMPTS_DEFINITIONS.slice(startIdx, startIdx + PAGE_SIZE);

  return { prompts };
}

/**
 * prompts/get ハンドラ
 */
export async function handleGetPrompt(args: Record<string, unknown>): Promise<{
  description?: string;
  messages: PromptMessage[];
}> {
  const { name, arguments: promptArgs } = args as {
    name?: string;
    arguments?: Record<string, string>;
  };

  if (!name) {
    throw new Error('name is required');
  }

  const prompt = PROMPTS_DEFINITIONS.find((p) => p.name === name);
  if (!prompt) {
    throw new Error(`Prompt not found: ${name}`);
  }

  // 必須引数のバリデーション
  if (prompt.arguments) {
    for (const arg of prompt.arguments) {
      if (arg.required && (!promptArgs || !(arg.name in promptArgs))) {
        throw new Error(`Required argument missing: ${arg.name}`);
      }
    }
  }

  const messages = generatePromptMessages(prompt, promptArgs);

  // exactOptionalPropertyTypes対応: undefinedは含めない
  return {
    ...(prompt.description !== undefined && { description: prompt.description }),
    messages,
  };
}

// ========== Tool Definitions ==========

export const TOOL_DEFINITIONS = [
  {
    name: 'pce.memory.policy.apply',
    description:
      'Initialize memory system with policy configuration. Call once at session start before using other tools. Configures boundary rules, redaction patterns, and rate limits.',
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
    name: 'pce.memory.observe',
    description:
      'Record a temporary observation with auto-expiry (default 30 days). Use for chat logs, tool outputs, file reads, API responses. Set extract.mode="single_claim_v0" to promote to permanent claim. Auto-detects and redacts PII/secrets.',
    inputSchema: {
      type: 'object',
      properties: {
        source_type: { type: 'string', enum: ['chat', 'tool', 'file', 'http', 'system'] },
        source_id: { type: 'string' },
        content: { type: 'string' },
        boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        actor: { type: 'string' },
        tags: { type: 'array', items: { type: 'string' } },
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
        ttl_days: { type: 'number', minimum: 1 },
        extract: {
          type: 'object',
          properties: {
            mode: { type: 'string', enum: ['noop', 'single_claim_v0'] },
          },
        },
      },
      required: ['source_type', 'content'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        observation_id: { type: 'string', description: 'Observation ID' },
        claim_ids: { type: 'array', items: { type: 'string' }, description: 'Extracted claim IDs' },
        effective_boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        content_stored: { type: 'boolean' },
        content_redacted: { type: 'boolean' },
        warnings: { type: 'array', items: { type: 'string' } },
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
        'observation_id',
        'claim_ids',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce.memory.upsert',
    description:
      'Register a permanent knowledge claim (never auto-deleted). Use for verified decisions, resolved errors, architectural patterns. Requires provenance.at timestamp. Prefer over observe for long-term, validated knowledge.',
    inputSchema: {
      type: 'object',
      properties: {
        text: { type: 'string' },
        kind: { type: 'string', enum: ['fact', 'preference', 'task', 'policy_hint'] },
        scope: { type: 'string', enum: ['session', 'project', 'principle'] },
        boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        content_hash: {
          type: 'string',
          pattern: '^sha256:[0-9a-f]{64}$',
          description:
            'Optional. SHA256 hash of text for deduplication. Auto-generated if omitted; validated against text if provided.',
        },
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
      required: ['text', 'kind', 'scope', 'boundary_class'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Claim ID' },
        is_new: { type: 'boolean', description: 'Whether this is a new claim' },
        content_hash: {
          type: 'string',
          description: 'SHA256 hash of text (auto-generated or provided)',
        },
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
    description:
      'Retrieve relevant knowledge for current task via hybrid search. Call before starting work to recall past decisions, patterns, and solutions. Returns ranked claims filtered by scope and boundary.',
    inputSchema: {
      type: 'object',
      properties: {
        scope: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Pace layer scopes to search',
        },
        allow: {
          type: 'array',
          items: { type: 'string' },
          description:
            'Policy allow tags to filter claims (e.g., ["answer:task", "tool:*"] or ["*"] for all). These are NOT boundary_class names. Default policy: public=["*"], internal=["answer:task", "tool:*"]',
        },
        top_k: { type: 'integer', minimum: 1, maximum: 50, description: 'Max claims to return' },
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
    description:
      'Validate and redact sensitive content before outputting to user. Checks for PII, secrets, and boundary policy violations. Returns sanitized payload safe for external use.',
    inputSchema: {
      type: 'object',
      properties: {
        payload: { type: 'string', description: 'Content to validate and potentially redact' },
        allow: {
          type: 'array',
          items: { type: 'string' },
          description:
            'Policy allow tags for boundary check (e.g., ["answer:task"] or ["*"]). NOT boundary_class names.',
        },
        scope: {
          type: 'string',
          enum: ['session', 'project', 'principle'],
          description: 'Pace layer scope for validation',
        },
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
    description:
      'Report knowledge quality after using activated claims. Send helpful when knowledge solved the problem, harmful if it caused errors, outdated if info was stale, duplicate if redundant.',
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
          description: 'Target directory path (default: .pce-shared at Git root if available)',
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
          description: 'Source directory path (default: .pce-shared at Git root if available)',
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
        since: {
          type: 'string',
          format: 'date-time',
          description:
            'Incremental import: only import claims with provenance.at >= since (ISO8601)',
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
                skipped_by_since: {
                  type: 'integer',
                  minimum: 0,
                  description: 'Skipped due to since filter',
                },
              },
              required: ['new', 'skipped_duplicate', 'upgraded_boundary', 'skipped_by_since'],
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
        manifest_updated: {
          type: 'boolean',
          description: 'Whether manifest.json was updated with last_pull_at',
        },
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
        'manifest_updated',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  // Phase 2: sync.status
  {
    name: 'pce.memory.sync.status',
    description: 'Get sync directory status including manifest, file counts, and validation state',
    inputSchema: {
      type: 'object',
      properties: {
        target_dir: {
          type: 'string',
          description: 'Target directory path (default: .pce-shared at Git root if available)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        exists: { type: 'boolean', description: 'Whether sync directory exists' },
        manifest: {
          type: 'object',
          properties: {
            version: { type: 'string' },
            pce_memory_version: { type: 'string' },
            last_push_at: { type: 'string', format: 'date-time' },
            last_push_policy_version: { type: 'string' },
            last_pull_at: { type: 'string', format: 'date-time' },
          },
          description: 'Manifest content (if exists)',
        },
        files: {
          type: 'object',
          properties: {
            claims: { type: 'integer', minimum: 0 },
            entities: { type: 'integer', minimum: 0 },
            relations: { type: 'integer', minimum: 0 },
          },
          required: ['claims', 'entities', 'relations'],
          description: 'File counts by type',
        },
        validation: {
          type: 'object',
          properties: {
            isValid: { type: 'boolean' },
            errors: { type: 'array', items: { type: 'string' } },
          },
          required: ['isValid', 'errors'],
          description: 'Validation status',
        },
        target_dir: { type: 'string', description: 'Actual target directory path' },
        policy_version: { type: 'string', description: 'Current policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'exists',
        'files',
        'validation',
        'target_dir',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
];

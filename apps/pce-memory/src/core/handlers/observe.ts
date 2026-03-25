/**
 * handleObserve – pce_memory_observe tool handler
 */

import * as crypto from 'node:crypto';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import type { Provenance } from '../../store/claims.js';
import {
  gcExpiredObservations,
  insertObservation,
  type InsertObservationInput,
  type ObservationSourceType,
} from '../../store/observations.js';
import { analyzeTextSensitivity, redactPiiText } from '../../audit/redactText.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import { getPolicy, getPolicyVersion, getStateType, canDoUpsert } from '../../state/memoryState.js';
import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
} from '../../state/layerScopeState.js';
import {
  createToolResult,
  err,
  validateStringE,
  hasPathTraversal,
  validateRequiredProvenance,
} from './shared.js';

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
    if (source_id !== undefined) {
      const sidResult = validateStringE('source_id', source_id, 2_048);
      if (E.isLeft(sidResult)) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', sidResult.left.message, reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }
    if (actor !== undefined) {
      const actorResult = validateStringE('actor', actor, 512);
      if (E.isLeft(actorResult)) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', actorResult.left.message, reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    if (typeof source_id === 'string' && hasPathTraversal(source_id)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'source_id contains path traversal segments', reqId),
          trace_id: traceId,
        },
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
    const mode = extractMode ?? 'noop';
    if (mode !== 'noop') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'invalid extract.mode', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // provenanceは任意。ただし存在する場合は at が必須
    if (provenance !== undefined) {
      const validatedProvenance = validateRequiredProvenance(provenance);
      if (!validatedProvenance.ok) {
        return createToolResult(
          {
            ...err('VALIDATION_ERROR', validatedProvenance.message, reqId),
            trace_id: traceId,
          },
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
      boundary_class: effectiveBoundaryClass,
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

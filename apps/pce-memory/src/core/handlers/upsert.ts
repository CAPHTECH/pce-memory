/**
 * handleUpsert - Register a durable claim with optional graph memory.
 */

import * as E from 'fp-ts/Either';
import type { Provenance } from '../../store/claims.js';
import { upsertClaim } from '../../store/claims.js';
import { upsertClaimWithEmbedding } from '../../store/claims.js';
import { getEmbeddingService, findSimilarActiveClaims } from '../../store/hybridSearch.js';
import { suggestRelatedClaimLinks } from '../../store/claimLinks.js';
import type { EntityInput } from '../../store/entities.js';
import type { RelationInput } from '../../store/relations.js';
import { isDomainError } from '../../domain/errors.js';
import type { ClaimKind, MemoryType } from '../../domain/types.js';
import { isValidMemoryType } from '../../domain/types.js';
import {
  getPolicyVersion,
  getStateType,
  transitionToHasClaimsFromDb,
} from '../../state/memoryState.js';
import {
  enterRequestScope,
  exitRequestScope,
  addResourceToCurrentScope,
} from '../../state/layerScopeState.js';
import { appendLog } from '../../store/logs.js';
import {
  createToolResult,
  err,
  getUnknownFields,
  validateUpsertInput,
  processGraphMemory,
  validateRequiredProvenance,
  validateStringE,
} from './shared.js';

export async function handleUpsert(args: Record<string, unknown>) {
  const {
    text,
    kind,
    scope,
    boundary_class,
    memory_type,
    content_hash,
    provenance,
    entities,
    relations,
  } = args as {
    text?: string;
    kind?: string;
    scope?: string;
    boundary_class?: string;
    memory_type?: string;
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
    const unknownFields = getUnknownFields(args, [
      'text',
      'kind',
      'scope',
      'boundary_class',
      'memory_type',
      'content_hash',
      'provenance',
      'entities',
      'relations',
    ]);
    if (unknownFields.length > 0) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `unknown fields: ${unknownFields.join(', ')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

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

    if (scope === 'project' || scope === 'principle') {
      const validatedProvenance = validateRequiredProvenance(provenance);
      if (!validatedProvenance.ok) {
        const message =
          validatedProvenance.message === 'provenance.at is required'
            ? 'provenance.at is required for non-session scope claims'
            : validatedProvenance.message;
        return createToolResult(
          {
            ...err('VALIDATION_ERROR', message, reqId),
            trace_id: traceId,
          },
          { isError: true }
        );
      }
    }

    if (memory_type !== undefined) {
      const mtResult = validateStringE('memory_type', memory_type, 128);
      if (E.isLeft(mtResult)) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', mtResult.left.message, reqId), trace_id: traceId },
          { isError: true }
        );
      }

      if (!isValidMemoryType(memory_type)) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'unknown memory_type', reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    // Claim登録（EmbeddingServiceがあれば埋め込みも生成）
    const claimInput = {
      text: text!,
      kind: kind as ClaimKind,
      scope: scope!,
      boundary_class: boundary_class!,
      ...(memory_type !== undefined ? { memory_type: memory_type as MemoryType } : {}),
      content_hash: validation.resolvedHash,
      ...(provenance !== undefined ? { provenance } : {}),
    };
    const embeddingService = getEmbeddingService();
    const { claim, isNew } = embeddingService
      ? await upsertClaimWithEmbedding(claimInput, embeddingService)
      : await upsertClaim(claimInput);

    // Graph Memory処理（ヘルパー関数に委譲）
    const graphResult = await processGraphMemory(claim.id, isNew, entities, relations);
    const suggestedLinks = isNew ? await suggestRelatedClaimLinks(claim.id) : [];
    const similarExisting = await findSimilarActiveClaims(claim.id).catch(() => []);

    // スコープへのリソース登録
    const addResult = addResourceToCurrentScope(scopeId, claim.id);
    if (E.isLeft(addResult)) {
      const isBenignDedupOwnershipConflict =
        !isNew &&
        addResult.left.code === 'VALIDATION_ERROR' &&
        addResult.left.message.includes('already owned by scope');
      if (!isBenignDedupOwnershipConflict) {
        console.error(`[Handler] Failed to add resource to scope: ${addResult.left.message}`);
      }
    }

    // 状態遷移
    await transitionToHasClaimsFromDb(isNew ? 1 : 0);

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
    const { entityCount, entityErrors, relationCount, relationErrors } = graphResult;
    const graphMemoryResult =
      entityCount > 0 || entityErrors.length > 0 || relationCount > 0 || relationErrors.length > 0
        ? {
            graph_memory: {
              entities: {
                success: entityCount,
                failed: entityErrors.length,
                ...(entityErrors.length > 0 && { errors: entityErrors }),
              },
              relations: {
                success: relationCount,
                failed: relationErrors.length,
                ...(relationErrors.length > 0 && { errors: relationErrors }),
              },
            },
          }
        : {};

    return createToolResult({
      id: claim.id,
      is_new: isNew,
      content_hash: validation.resolvedHash,
      suggested_links: suggestedLinks,
      ...(similarExisting.length > 0 ? { similar_existing: similarExisting } : {}),
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
      {
        ...err(
          isDomainError(e) && e.code === 'CONTENT_HASH_COLLISION'
            ? 'VALIDATION_ERROR'
            : 'UPSERT_FAILED',
          msg,
          reqId
        ),
        trace_id: traceId,
      },
      { isError: true }
    );
  } finally {
    exitRequestScope(scopeId);
  }
}

/**
 * handlePromote – promote a distill candidate to a durable claim.
 */

import * as crypto from 'node:crypto';
import { boundaryValidate } from '@pce/boundary';
import * as E from 'fp-ts/Either';

import {
  createToolResult,
  err,
  validateRequiredProvenance,
  acquirePromotionLock,
  getPromotionCandidateConflictMessage,
  parseJsonObject,
  isDurableScope,
  isDurableBoundaryClass,
} from './shared.js';

import {
  upsertClaim,
  upsertClaimWithEmbedding,
  findClaimByContentHash,
} from '../../store/claims.js';
import type { Provenance } from '../../store/claims.js';
import {
  findSimilarActiveClaims,
  getEmbeddingService,
} from '../../store/hybridSearch.js';
import { suggestRelatedClaimLinks } from '../../store/claimLinks.js';
import { insertEvidence } from '../../store/evidence.js';
import {
  acceptPromotionQueueRow,
  findPromotionQueueRowById,
} from '../../store/promotionQueue.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import { isDomainError } from '../../domain/errors.js';
import { isValidClaimKind, isValidMemoryType } from '../../domain/types.js';
import {
  getPolicy,
  getPolicyVersion,
  getStateType,
  canDoUpsert,
  transitionToHasClaims,
} from '../../state/memoryState.js';
import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
} from '../../state/layerScopeState.js';
import { getConnection } from '../../db/connection.js';

export async function handlePromote(args: Record<string, unknown>) {
  const { candidate_id, provenance, reviewers, review_note } = args as {
    candidate_id?: unknown;
    provenance?: unknown;
    reviewers?: unknown;
    review_note?: unknown;
  };

  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
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
  let transactionOpen = false;
  let releasePromotionLock: (() => void) | null = null;

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

    if (typeof candidate_id !== 'string' || candidate_id.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'candidate_id is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const validatedProvenance = validateRequiredProvenance(provenance);
    if (!validatedProvenance.ok) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', validatedProvenance.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (review_note !== undefined && typeof review_note !== 'string') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'review_note must be a string', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (
      reviewers !== undefined &&
      (!Array.isArray(reviewers) || reviewers.some((reviewer) => typeof reviewer !== 'string'))
    ) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'reviewers must be string[]', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    releasePromotionLock = await acquirePromotionLock(candidate_id);

    const candidate = await findPromotionQueueRowById(candidate_id);
    if (!candidate) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'candidate not found', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (candidate.status !== 'pending') {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            `candidate status must be pending (got ${candidate.status})`,
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (!isValidClaimKind(candidate.proposed_kind)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate proposed_kind is invalid', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (!isDurableScope(candidate.proposed_scope)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate proposed_scope is invalid', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (!isDurableBoundaryClass(candidate.proposed_boundary_class)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate proposed_boundary_class is invalid', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (candidate.proposed_memory_type === 'evidence') {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'candidate proposed_memory_type evidence cannot become a durable claim',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (candidate.proposed_memory_type && !isValidMemoryType(candidate.proposed_memory_type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate proposed_memory_type is invalid', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (candidate.proposed_boundary_class === 'secret') {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'secret candidates cannot be promoted to durable claims',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const policy = getPolicy();
    const boundaryCheck = boundaryValidate(
      {
        payload: candidate.distilled_text,
        allow: policy.boundary_classes[candidate.proposed_boundary_class]?.allow ?? [],
        scope: candidate.proposed_scope,
      },
      policy
    );
    if (!boundaryCheck.allowed) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate failed boundary validation', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const candidateLineage = parseJsonObject<Record<string, unknown>>(candidate.provenance, {});
    const sourceObservationIds = Array.isArray(candidateLineage['source_observation_ids'])
      ? (candidateLineage['source_observation_ids'] as string[])
      : [];
    const sourceClaimIds = Array.isArray(candidateLineage['source_claim_ids'])
      ? (candidateLineage['source_claim_ids'] as string[])
      : [];
    const lineageActiveContextId =
      typeof candidateLineage['active_context_id'] === 'string'
        ? (candidateLineage['active_context_id'] as string)
        : undefined;
    const mergedPromotionNote = [validatedProvenance.value.note, review_note]
      .filter((value): value is string => typeof value === 'string' && value.length > 0)
      .join(' | ');
    const promotionProvenance: Provenance = mergedPromotionNote
      ? { ...validatedProvenance.value, note: mergedPromotionNote }
      : validatedProvenance.value;

    const existingClaim = await findClaimByContentHash(candidate.candidate_hash);
    if (existingClaim) {
      const conflictMessage = getPromotionCandidateConflictMessage(candidate, existingClaim);
      if (conflictMessage) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', conflictMessage, reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    const conn = await getConnection();
    await conn.run('BEGIN TRANSACTION');
    transactionOpen = true;

    const embeddingService = getEmbeddingService();
    const { claim, isNew } = embeddingService
      ? await upsertClaimWithEmbedding(
          {
            text: candidate.distilled_text,
            kind: candidate.proposed_kind,
            scope: candidate.proposed_scope,
            boundary_class: candidate.proposed_boundary_class,
            ...(candidate.proposed_memory_type
              ? { memory_type: candidate.proposed_memory_type }
              : {}),
            content_hash: candidate.candidate_hash,
            provenance: promotionProvenance,
          },
          embeddingService
        )
      : await upsertClaim({
          text: candidate.distilled_text,
          kind: candidate.proposed_kind,
          scope: candidate.proposed_scope,
          boundary_class: candidate.proposed_boundary_class,
          ...(candidate.proposed_memory_type
            ? { memory_type: candidate.proposed_memory_type }
            : {}),
          content_hash: candidate.candidate_hash,
          provenance: promotionProvenance,
        });

    const promotedClaimConflict = getPromotionCandidateConflictMessage(candidate, claim);
    if (promotedClaimConflict) {
      throw new Error(promotedClaimConflict);
    }

    if (isNew) {
      const evidenceSources = new Set(sourceObservationIds);
      for (const observationId of evidenceSources) {
        await insertEvidence({
          id: `evd_${crypto.randomUUID().slice(0, 8)}`,
          claim_id: claim.id,
          source_type: 'observation',
          source_id: observationId,
          snippet: `promotion candidate ${candidate.id}`,
          at: validatedProvenance.value.at,
        });
      }

      for (const sourceClaimId of new Set(sourceClaimIds)) {
        await insertEvidence({
          id: `evd_${crypto.randomUUID().slice(0, 8)}`,
          claim_id: claim.id,
          source_type: 'claim',
          source_id: sourceClaimId,
          snippet: `promotion candidate ${candidate.id}`,
          at: validatedProvenance.value.at,
        });
      }

      if (lineageActiveContextId) {
        await insertEvidence({
          id: `evd_${crypto.randomUUID().slice(0, 8)}`,
          claim_id: claim.id,
          source_type: 'active_context',
          source_id: lineageActiveContextId,
          snippet: `promotion candidate ${candidate.id}`,
          at: validatedProvenance.value.at,
        });
      }
    }

    const accepted = await acceptPromotionQueueRow(candidate.id, {
      accepted_claim_id: claim.id,
      reviewers: reviewers ? JSON.stringify(reviewers as string[]) : null,
      resolved_at: validatedProvenance.value.at,
      provenance: JSON.stringify({
        ...candidateLineage,
        promotion: {
          provenance: validatedProvenance.value,
          reviewers: reviewers ?? [],
          review_note: review_note ?? null,
        },
      }),
    });
    if (!accepted) {
      await conn.run('ROLLBACK');
      transactionOpen = false;
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'candidate was resolved concurrently', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const similarExisting = await findSimilarActiveClaims(claim.id).catch(() => []);

    await appendLog({
      id: `log_${reqId}`,
      op: 'promote',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    await conn.run('COMMIT');
    transactionOpen = false;

    transitionToHasClaims(isNew);
    const suggestedLinks = isNew ? await suggestRelatedClaimLinks(claim.id) : [];

    return createToolResult({
      claim_id: claim.id,
      target_layer: candidate.target_layer,
      is_new: isNew,
      promoted_from: candidate.id,
      rollback_token: claim.id,
      suggested_links: suggestedLinks,
      ...(similarExisting.length > 0 ? { similar_existing: similarExisting } : {}),
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    if (transactionOpen) {
      try {
        const conn = await getConnection();
        await conn.run('ROLLBACK');
      } catch {
        // best-effort rollback
      }
    }
    try {
      await appendLog({
        id: `log_${reqId}`,
        op: 'promote',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
    } catch {
      // best-effort failure audit
    }
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      {
        ...err(
          isDomainError(e) && e.code === 'CONTENT_HASH_COLLISION'
            ? 'VALIDATION_ERROR'
            : 'DB_ERROR',
          msg,
          reqId
        ),
        trace_id: traceId,
      },
      { isError: true }
    );
  } finally {
    if (releasePromotionLock) {
      releasePromotionLock();
    }
    exitRequestScope(scopeId);
  }
}

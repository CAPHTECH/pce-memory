/**
 * Handler for pce_memory_distill tool.
 *
 * Distills raw observations and/or existing claims into a promotion candidate.
 */

import { boundaryValidate } from '@pce/boundary';
import { computeContentHash } from '@pce/embeddings';
import type { Claim } from '../../store/claims.js';
import { findClaimsByIds } from '../../store/claims.js';
import { getEvidenceForClaims } from '../../store/evidence.js';
import { findObservationsByIds } from '../../store/observations.js';
import { findActiveContextById } from '../../store/activeContext.js';
import { insertPromotionQueueRow } from '../../store/promotionQueue.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import { isValidClaimKind, isValidMemoryType } from '../../domain/types.js';
import type { ClaimKind, MemoryType } from '../../domain/types.js';
import * as E from 'fp-ts/Either';
import {
  getPolicy,
  getPolicyVersion,
  getStateType,
  canDoUpsert,
} from '../../state/memoryState.js';
import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
} from '../../state/layerScopeState.js';

import {
  createToolResult,
  err,
  isDurableScope,
  isDurableBoundaryClass,
  DEFAULT_PROMOTION_MAX_SOURCES,
  DEFAULT_PROMOTION_MAX_BYTES,
  readPositiveIntEnv,
  resolveObservationSourceText,
  resolveClaimSourceText,
  getMostRestrictiveBoundary,
  inferDurableScope,
  inferMemoryTypeForKind,
  mapScopeToLayer,
  mapDurableScopeToTargetLayer,
  dedupeStrings,
  type DurableScope,
  type DurableBoundaryClass,
} from './shared.js';

export async function handleDistill(args: Record<string, unknown>) {
  const {
    source_observation_ids,
    source_claim_ids,
    active_context_id,
    proposed_kind,
    proposed_scope,
    proposed_memory_type,
    note,
  } = args as {
    source_observation_ids?: unknown;
    source_claim_ids?: unknown;
    active_context_id?: unknown;
    proposed_kind?: unknown;
    proposed_scope?: unknown;
    proposed_memory_type?: unknown;
    note?: unknown;
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

    const rawObservationIds =
      source_observation_ids === undefined
        ? []
        : Array.isArray(source_observation_ids) &&
            source_observation_ids.every((value) => typeof value === 'string')
          ? (source_observation_ids as string[])
          : null;
    const rawClaimIds =
      source_claim_ids === undefined
        ? []
        : Array.isArray(source_claim_ids) &&
            source_claim_ids.every((value) => typeof value === 'string')
          ? (source_claim_ids as string[])
          : null;

    if (rawObservationIds === null || rawClaimIds === null) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'source_observation_ids and source_claim_ids must be string[]',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const observationIds = dedupeStrings(rawObservationIds);
    const claimIds = dedupeStrings(rawClaimIds);

    if (active_context_id !== undefined && typeof active_context_id !== 'string') {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'active_context_id must be a string', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (note !== undefined && typeof note !== 'string') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'note must be a string', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (observationIds.length === 0 && claimIds.length === 0 && active_context_id === undefined) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'at least one source is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (proposed_kind !== undefined && !isValidClaimKind(proposed_kind)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown proposed_kind', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (proposed_scope !== undefined && !isDurableScope(proposed_scope)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'proposed_scope must be project or principle', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (proposed_memory_type !== undefined) {
      if (!isValidMemoryType(proposed_memory_type)) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'unknown proposed_memory_type', reqId), trace_id: traceId },
          { isError: true }
        );
      }
      if (proposed_memory_type === 'evidence') {
        return createToolResult(
          {
            ...err(
              'VALIDATION_ERROR',
              'proposed_memory_type evidence is reserved for micro memory',
              reqId
            ),
            trace_id: traceId,
          },
          { isError: true }
        );
      }
    }

    const observations = await findObservationsByIds(observationIds);
    if (observations.length !== observationIds.length) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'one or more observation sources were not found', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    const observationsById = new Map(
      observations.map((observation) => [observation.id, observation])
    );

    const sourceClaims = await findClaimsByIds(claimIds);
    if (sourceClaims.length !== claimIds.length) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'one or more claim sources were not found', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    const sourceClaimsById = new Map(sourceClaims.map((claim) => [claim.id, claim]));

    const activeContext = active_context_id
      ? await findActiveContextById(active_context_id)
      : undefined;
    if (active_context_id && !activeContext) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'active_context_id not found', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const activeContextClaimIds = activeContext?.claims.map((claim) => claim.id) ?? [];
    const activeContextClaims = await findClaimsByIds(activeContextClaimIds);
    const activeContextClaimsById = new Map(activeContextClaims.map((claim) => [claim.id, claim]));

    const allClaims = new Map<string, Claim>();
    for (const claimId of claimIds) {
      const claim = sourceClaimsById.get(claimId);
      if (claim) {
        allClaims.set(claim.id, claim);
      }
    }
    for (const claimId of activeContextClaimIds) {
      const claim = activeContextClaimsById.get(claimId);
      if (claim) {
        allClaims.set(claim.id, claim);
      }
    }

    const sourceTexts: string[] = [];
    const sourceBoundaries: DurableBoundaryClass[] = [];
    const sourceIds = new Set<string>();
    const sourceLayers = new Set<string>();

    for (const observationId of observationIds) {
      const observation = observationsById.get(observationId);
      if (!observation) continue;
      sourceTexts.push(resolveObservationSourceText(observation));
      sourceIds.add(observation.id);
      sourceLayers.add('micro');
      sourceBoundaries.push(
        isDurableBoundaryClass(observation.boundary_class) ? observation.boundary_class : 'internal'
      );
    }

    for (const claim of allClaims.values()) {
      sourceTexts.push(resolveClaimSourceText(claim));
      sourceIds.add(claim.id);
      sourceLayers.add(mapScopeToLayer(claim.scope));
      sourceBoundaries.push(
        isDurableBoundaryClass(claim.boundary_class) ? claim.boundary_class : 'internal'
      );
    }

    if (activeContext) {
      sourceIds.add(activeContext.id);
      sourceLayers.add('micro');
    }

    if (sourceTexts.length === 0) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'no source text available to distill', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const maxSources = readPositiveIntEnv(
      'PCE_PROMOTION_MAX_SOURCES',
      DEFAULT_PROMOTION_MAX_SOURCES
    );
    if (sourceTexts.length > maxSources) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `too many sources to distill (max ${maxSources})`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const sourceClaimIdsForEvidence = [...allClaims.keys()];
    const evidenceByClaim = await getEvidenceForClaims(sourceClaimIdsForEvidence);
    const evidenceIds = new Set<string>(observationIds);
    for (const claimEvidence of evidenceByClaim.values()) {
      for (const evidence of claimEvidence) {
        evidenceIds.add(evidence.id);
      }
    }

    const commonClaimKinds = new Set(
      [...allClaims.values()]
        .map((claim) => claim.kind)
        .filter((kind): kind is ClaimKind => isValidClaimKind(kind))
    );
    const resolvedKind =
      (proposed_kind as ClaimKind | undefined) ??
      (commonClaimKinds.size === 1 ? [...commonClaimKinds][0]! : 'fact');

    const explicitMemoryType = proposed_memory_type as MemoryType | undefined;
    const commonMemoryTypes = new Set(
      [...allClaims.values()]
        .map((claim) => claim.memory_type)
        .filter(
          (memoryType): memoryType is MemoryType => memoryType !== null && memoryType !== undefined
        )
    );
    const resolvedMemoryType =
      explicitMemoryType ??
      (commonMemoryTypes.size === 1 && !commonMemoryTypes.has('evidence')
        ? [...commonMemoryTypes][0]
        : inferMemoryTypeForKind(resolvedKind));

    const resolvedScope =
      (proposed_scope as DurableScope | undefined) ??
      inferDurableScope(resolvedKind, resolvedMemoryType);
    const targetLayer = mapDurableScopeToTargetLayer(resolvedScope);
    const proposedBoundaryClass = getMostRestrictiveBoundary(sourceBoundaries);
    const distilledText = sourceTexts.join('\n\n---\n\n');
    const maxPromotionBytes = readPositiveIntEnv(
      'PCE_PROMOTION_MAX_BYTES',
      DEFAULT_PROMOTION_MAX_BYTES
    );
    if (Buffer.byteLength(distilledText, 'utf8') > maxPromotionBytes) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            `distilled_text too large (max ${maxPromotionBytes} bytes)`,
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    const candidateHash = `sha256:${computeContentHash(distilledText)}`;
    const policy = getPolicy();
    const boundaryCheck = boundaryValidate(
      {
        payload: distilledText,
        allow: policy.boundary_classes[proposedBoundaryClass]?.allow ?? [],
        scope: resolvedScope,
      },
      policy
    );

    const createdAt = new Date().toISOString();
    const candidateId = `pq_${crypto.randomUUID().slice(0, 8)}`;
    const invariantCheckResults = {
      boundary_monotonicity: {
        passed: true,
        max_source_boundary_class: proposedBoundaryClass,
      },
      boundary_validate: boundaryCheck,
      source_counts: {
        observations: observations.length,
        claims: sourceClaims.length,
        active_context_claims: activeContextClaims.length,
      },
    };

    await insertPromotionQueueRow({
      id: candidateId,
      source_layer: sourceLayers.size === 1 ? [...sourceLayers][0]! : 'mixed',
      target_layer: targetLayer,
      source_ids: JSON.stringify([...sourceIds]),
      distilled_text: distilledText,
      candidate_hash: candidateHash,
      proposed_kind: resolvedKind,
      proposed_scope: resolvedScope,
      proposed_boundary_class: proposedBoundaryClass,
      proposed_memory_type: resolvedMemoryType ?? null,
      provenance: JSON.stringify({
        distilled_at: createdAt,
        note,
        source_observation_ids: observationIds,
        source_claim_ids: claimIds,
        active_context_id: active_context_id,
      }),
      evidence_ids: JSON.stringify([...evidenceIds]),
      policy_version_checked: getPolicyVersion(),
      boundary_check_result: JSON.stringify(boundaryCheck),
      status: 'pending',
      created_at: createdAt,
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'distill',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      candidate_id: candidateId,
      distilled_text: distilledText,
      proposed_kind: resolvedKind,
      proposed_scope: resolvedScope,
      proposed_memory_type: resolvedMemoryType ?? null,
      proposed_boundary_class: proposedBoundaryClass,
      status: 'pending',
      invariant_check_results: invariantCheckResults,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'distill',
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

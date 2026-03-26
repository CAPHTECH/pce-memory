/**
 * Rollback handler: append-only rollback of durable claims.
 */

import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import {
  createToolResult,
  err,
  validateRequiredProvenance,
  mapScopeToLayer,
  type ToolResult,
} from './shared.js';
import { findClaimById } from '../../store/claims.js';
import { getEvidenceForClaims } from '../../store/evidence.js';
import { insertPromotionQueueRow } from '../../store/promotionQueue.js';
import { findRollbackRecordByClaimId } from '../../store/promotionQueue.js';
import { collectRollbackTopologyBlastRadius } from '../../store/rollbackTopology.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { getStateType, canDoUpsert, getPolicyVersion } from '../../state/memoryState.js';
import {
  enterRequestScope,
  exitRequestScope,
  isInActiveScope,
} from '../../state/layerScopeState.js';
import { stateError } from '../../domain/stateMachine.js';

export async function handleRollback(args: Record<string, unknown>): Promise<ToolResult> {
  const { claim_id, reason, provenance } = args as {
    claim_id?: unknown;
    reason?: unknown;
    provenance?: unknown;
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

    if (typeof claim_id !== 'string' || claim_id.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'claim_id is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (typeof reason !== 'string' || reason.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'reason is required', reqId), trace_id: traceId },
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

    const claim = await findClaimById(claim_id);
    if (!claim) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'claim not found', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const existingRollback = await findRollbackRecordByClaimId(claim.id);
    if (claim.tombstone || existingRollback) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'claim is already rolled back', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    const blastRadius = await collectRollbackTopologyBlastRadius(claim.id);
    const rollbackId = `rbk_${crypto.randomUUID().slice(0, 8)}`;
    const evidenceMap = await getEvidenceForClaims([claim.id]);
    const evidenceIds = (evidenceMap.get(claim.id) ?? []).map((evidence) => evidence.id);
    await insertPromotionQueueRow({
      id: rollbackId,
      source_layer: mapScopeToLayer(claim.scope),
      target_layer: mapScopeToLayer(claim.scope),
      source_ids: JSON.stringify([claim.id]),
      distilled_text: claim.text,
      candidate_hash: `sha256:${computeContentHash(`rollback:${claim.id}:${reason}:${validatedProvenance.value.at}`)}`,
      proposed_kind: claim.kind,
      proposed_scope: claim.scope,
      proposed_boundary_class: claim.boundary_class,
      proposed_memory_type: claim.memory_type ?? null,
      provenance: JSON.stringify({
        rollback_of: claim.id,
        reason,
        provenance: validatedProvenance.value,
      }),
      evidence_ids: JSON.stringify(evidenceIds),
      policy_version_checked: getPolicyVersion(),
      boundary_check_result: JSON.stringify({ allowed: true, rollback: true }),
      status: 'rolled_back',
      created_at: validatedProvenance.value.at,
      resolved_at: validatedProvenance.value.at,
      accepted_claim_id: claim.id,
      rejected_reason: reason,
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'rollback',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      rollback_id: rollbackId,
      superseded_claim_id: claim.id,
      blast_radius: blastRadius,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    }, { useSafeStringify: true });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'rollback',
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

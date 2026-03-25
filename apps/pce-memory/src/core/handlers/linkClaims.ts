/**
 * Handler for pce_memory_link_claims tool.
 *
 * Links two claims together with a typed relationship.
 */

import { createToolResult, err, type ToolResult } from './shared.js';
import { findClaimById } from '../../store/claims.js';
import { isValidClaimLinkType, upsertClaimLink } from '../../store/claimLinks.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import { getStateType, canDoUpsert, getPolicyVersion } from '../../state/memoryState.js';

export async function handleLinkClaims(args: Record<string, unknown>): Promise<ToolResult> {
  const { source_claim_id, target_claim_id, link_type, confidence } = args as {
    source_claim_id?: unknown;
    target_claim_id?: unknown;
    link_type?: unknown;
    confidence?: unknown;
  };

  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    if (!canDoUpsert()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
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

    if (typeof source_claim_id !== 'string' || source_claim_id.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'source_claim_id is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (typeof target_claim_id !== 'string' || target_claim_id.length === 0) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'target_claim_id is required', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (!isValidClaimLinkType(link_type)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'link_type must be a supported claim link type', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (source_claim_id === target_claim_id) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'source_claim_id and target_claim_id must differ', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (
      confidence !== undefined &&
      (typeof confidence !== 'number' ||
        !Number.isFinite(confidence) ||
        confidence < 0 ||
        confidence > 1)
    ) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'confidence must be a number between 0 and 1', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const [sourceClaim, targetClaim] = await Promise.all([
      findClaimById(source_claim_id),
      findClaimById(target_claim_id),
    ]);
    if (!sourceClaim || !targetClaim) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'source_claim_id and target_claim_id must exist', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const { link, isNew } = await upsertClaimLink({
      source_claim_id,
      target_claim_id,
      link_type,
      ...(typeof confidence === 'number' ? { confidence } : {}),
      created_by: 'client',
    });

    await appendLog({
      id: `log_${reqId}`,
      op: 'link_claims',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      id: link.id,
      is_new: isNew,
      source_claim_id: link.source_claim_id,
      target_claim_id: link.target_claim_id,
      link_type: link.link_type,
      confidence: link.confidence,
      created_by: link.created_by ?? 'client',
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'link_claims',
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
  }
}

/**
 * Feedback and boundary-validation handlers.
 */

import { boundaryValidate } from '@pce/boundary';
import { createToolResult, err, type ToolResult } from './shared.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { findClaimById, updateClaimStatus } from '../../store/claims.js';
import { recordFeedback } from '../../store/feedback.js';
import { updateCritic } from '../../store/critic.js';
import { stateError } from '../../domain/stateMachine.js';
import {
  FEEDBACK_SIGNALS,
  isValidFeedbackSignal,
} from '../../domain/types.js';
import type { FeedbackSignal } from '../../domain/types.js';
import {
  getPolicy,
  getPolicyVersion,
  getStateType,
  canDoFeedback,
  getActiveContextId,
} from '../../state/memoryState.js';

export async function handleBoundaryValidate(args: Record<string, unknown>): Promise<ToolResult> {
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

export async function handleFeedback(args: Record<string, unknown>): Promise<ToolResult> {
  const { claim_id, signal, score } = args as {
    claim_id?: string;
    signal?: unknown;
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
    if (!isValidFeedbackSignal(signal)) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            `signal must be one of ${FEEDBACK_SIGNALS.join('|')}`,
            reqId
          ),
          trace_id: traceId,
        },
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
    const feedbackSignal = signal as FeedbackSignal;
    if (feedbackSignal === 'completed' && exists.memory_type !== 'working_state') {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'signal=completed is only allowed for working_state claims',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    const activeContextId = getActiveContextId();
    const feedbackInput: {
      claim_id: string;
      signal: FeedbackSignal;
      score?: number;
      active_context_id?: string;
    } = {
      claim_id,
      signal: feedbackSignal,
      ...(score !== undefined && { score }),
      ...(activeContextId !== undefined && { active_context_id: activeContextId }),
    };
    const res = await recordFeedback(feedbackInput);
    if (feedbackSignal === 'completed') {
      await updateClaimStatus(claim_id, 'completed');
    }

    const criticDelta =
      feedbackSignal === 'helpful'
        ? 1
        : feedbackSignal === 'harmful'
          ? -1
          : feedbackSignal === 'outdated' || feedbackSignal === 'duplicate'
            ? -0.5
            : undefined;
    if (criticDelta !== undefined) {
      await updateCritic(claim_id, criticDelta, 0, 5);
    }

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
      claim_id,
      signal: feedbackSignal,
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

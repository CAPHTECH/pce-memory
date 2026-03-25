/**
 * Health handler: knowledge base health report.
 */

import { createToolResult, err, type ToolResult } from './shared.js';
import { computeHealthReport } from '../../store/health.js';
import { appendLog } from '../../store/logs.js';
import { canDoQuery, getPolicyVersion, getStateType } from '../../state/memoryState.js';
import { stateError } from '../../domain/stateMachine.js';
import { checkAndConsume } from '../../store/rate.js';

/**
 * 知識ベースの健全性レポートを生成
 */
export async function handleHealth(_args: Record<string, unknown>): Promise<ToolResult> {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    if (!canDoQuery()) {
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

    const report = await computeHealthReport();

    await appendLog({
      id: `log_${reqId}`,
      op: 'health',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      ...report,
      policy_version: getPolicyVersion(),
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'health',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('HEALTH_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

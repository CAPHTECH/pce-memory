/**
 * State-related handlers: policy_apply and get_state.
 */

import * as E from 'fp-ts/Either';
import { createToolResult, err, type ToolResult } from './shared.js';
import { appendLog } from '../../store/logs.js';
import { applyPolicyOp, getPolicyVersion, getStateSummary } from '../../state/memoryState.js';
import { getLayerScopeSummary } from '../../state/layerScopeState.js';

export async function handlePolicyApply(args: Record<string, unknown>): Promise<ToolResult> {
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

export async function handleGetState(args: Record<string, unknown>): Promise<ToolResult> {
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

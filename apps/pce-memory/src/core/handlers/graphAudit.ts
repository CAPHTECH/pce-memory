import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { getPolicyVersion, getStateType } from '../../state/memoryState.js';
import { createToolResult, err, type ToolResult } from './shared.js';
import { auditGraph, type GraphAuditOptions } from '../../store/graphAudit.js';

function readPositiveInteger(value: unknown): number | undefined {
  return typeof value === 'number' && Number.isInteger(value) && value > 0 ? value : undefined;
}

export async function handleGraphAudit(args: Record<string, unknown> = {}): Promise<ToolResult> {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    const options: GraphAuditOptions = {};
    const minSupersessionChainLength = readPositiveInteger(
      args['min_supersession_chain_length']
    );
    const repeatedCoactivationThreshold = readPositiveInteger(
      args['repeated_coactivation_threshold']
    );
    const genericHubDegreeThreshold = readPositiveInteger(args['generic_hub_degree_threshold']);
    const maxFindingsPerKind = readPositiveInteger(args['max_findings_per_kind']);
    if (
      (args['min_supersession_chain_length'] !== undefined &&
        minSupersessionChainLength === undefined) ||
      (args['repeated_coactivation_threshold'] !== undefined &&
        repeatedCoactivationThreshold === undefined) ||
      (args['generic_hub_degree_threshold'] !== undefined &&
        genericHubDegreeThreshold === undefined) ||
      (args['max_findings_per_kind'] !== undefined && maxFindingsPerKind === undefined)
    ) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'graph audit thresholds must be positive integers',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (minSupersessionChainLength !== undefined) {
      options.minSupersessionChainLength = minSupersessionChainLength;
    }
    if (repeatedCoactivationThreshold !== undefined) {
      options.repeatedCoactivationThreshold = repeatedCoactivationThreshold;
    }
    if (genericHubDegreeThreshold !== undefined) {
      options.genericHubDegreeThreshold = genericHubDegreeThreshold;
    }
    if (maxFindingsPerKind !== undefined) {
      options.maxFindingsPerKind = maxFindingsPerKind;
    }

    const report = await auditGraph(options);

    await appendLog({
      id: `log_${reqId}`,
      op: 'graph_audit',
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
    }, { useSafeStringify: true });
  } catch (error: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'graph_audit',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const message = error instanceof Error ? error.message : String(error);
    return createToolResult(
      { ...err('DB_ERROR', message, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

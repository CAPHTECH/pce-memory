/**
 * MCP Tool Handlers - Thin Dispatcher
 *
 * デーモンモード/stdioモード両方から利用可能なハンドラ実装。
 * 各ハンドラはhandlers/ディレクトリのモジュールに分割されている。
 * このファイルはdispatchToolとすべてのハンドラ/型のre-exportを提供する。
 */

import { createToolResult, type ToolResult } from './handlers/shared.js';

// Re-export shared types
export type { ToolResult } from './handlers/shared.js';

// Re-export individual handlers
export { handlePolicyApply, handleGetState } from './handlers/state.js';
export { handleUpsert } from './handlers/upsert.js';
export { handleObserve } from './handlers/observe.js';
export { handleDistill } from './handlers/distill.js';
export { handlePromote } from './handlers/promote.js';
export { handleRollback } from './handlers/rollback.js';
export { handleLinkClaims } from './handlers/linkClaims.js';
export { handleActivate } from './handlers/activate.js';
export { handleBoundaryValidate, handleFeedback } from './handlers/feedback.js';
export {
  handleUpsertEntity,
  handleUpsertRelation,
  handleQueryEntity,
  handleQueryRelation,
} from './handlers/graph.js';
export { handleHealth } from './handlers/health.js';
export { handleSyncPush, handleSyncPull, handleSyncStatus } from './handlers/sync.js';

// Re-export prompts
export type { PromptDefinition, PromptMessage } from './handlers/prompts.js';
export { PROMPTS_DEFINITIONS, handleListPrompts, handleGetPrompt } from './handlers/prompts.js';

// Re-export tool definitions
export { TOOL_DEFINITIONS } from './handlers/toolDefinitions.js';

// Import handlers for the dispatcher
import { handlePolicyApply, handleGetState } from './handlers/state.js';
import { handleUpsert } from './handlers/upsert.js';
import { handleObserve } from './handlers/observe.js';
import { handleDistill } from './handlers/distill.js';
import { handlePromote } from './handlers/promote.js';
import { handleRollback } from './handlers/rollback.js';
import { handleLinkClaims } from './handlers/linkClaims.js';
import { handleActivate } from './handlers/activate.js';
import { handleBoundaryValidate, handleFeedback } from './handlers/feedback.js';
import {
  handleUpsertEntity,
  handleUpsertRelation,
  handleQueryEntity,
  handleQueryRelation,
} from './handlers/graph.js';
import { handleHealth } from './handlers/health.js';
import { handleSyncPush, handleSyncPull, handleSyncStatus } from './handlers/sync.js';

// ========== Tool Dispatcher ==========

/**
 * ツール名に基づいてハンドラをディスパッチ
 */
export async function dispatchTool(
  name: string,
  args: Record<string, unknown>
): Promise<ToolResult> {
  switch (name) {
    case 'pce_memory_policy_apply':
      return handlePolicyApply(args);
    case 'pce_memory_observe':
      return handleObserve(args);
    case 'pce_memory_distill':
      return handleDistill(args);
    case 'pce_memory_promote':
      return handlePromote(args);
    case 'pce_memory_rollback':
      return handleRollback(args);
    case 'pce_memory_upsert':
      return handleUpsert(args);
    case 'pce_memory_link_claims':
      return handleLinkClaims(args);
    case 'pce_memory_upsert_entity':
      return handleUpsertEntity(args);
    case 'pce_memory_upsert_relation':
      return handleUpsertRelation(args);
    case 'pce_memory_query_entity':
      return handleQueryEntity(args);
    case 'pce_memory_query_relation':
      return handleQueryRelation(args);
    case 'pce_memory_activate':
      return handleActivate(args);
    case 'pce_memory_boundary_validate':
      return handleBoundaryValidate(args);
    case 'pce_memory_feedback':
      return handleFeedback(args);
    case 'pce_memory_state':
      return handleGetState(args);
    case 'pce_memory_health':
      return handleHealth(args);
    // Sync Tools (Issue #18)
    case 'pce_memory_sync_push':
      return handleSyncPush(args);
    case 'pce_memory_sync_pull':
      return handleSyncPull(args);
    case 'pce_memory_sync_status':
      return handleSyncStatus(args);
    default:
      return createToolResult(
        { error: { code: 'UNKNOWN_TOOL', message: `Unknown tool: ${name}` } },
        { isError: true }
      );
  }
}

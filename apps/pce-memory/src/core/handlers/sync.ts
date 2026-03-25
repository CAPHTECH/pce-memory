/**
 * Sync handlers: push, pull, and status (Issue #18).
 */

import * as E from 'fp-ts/Either';
import { createToolResult, err, hasPathTraversal, type ToolResult } from './shared.js';
import { appendLog } from '../../store/logs.js';
import {
  canDoQuery,
  getPolicyVersion,
  getStateType,
  transitionToHasClaims,
} from '../../state/memoryState.js';
import { stateError } from '../../domain/stateMachine.js';
import { checkAndConsume } from '../../store/rate.js';
import {
  executePush,
  executePull,
  executeStatus,
  type PushOptions,
  type PullOptions,
  type StatusOptions,
  type Scope,
  type BoundaryClass,
} from '../../sync/index.js';

/**
 * Sync Push: ローカルDBから.pce-shared/へエクスポート
 */
export async function handleSyncPush(args: Record<string, unknown>): Promise<ToolResult> {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 引数の取得
    const {
      target_dir,
      scope_filter,
      boundary_filter,
      since,
      include_entities,
      include_relations,
    } = args as {
      target_dir?: string;
      scope_filter?: string[];
      boundary_filter?: string[];
      since?: string;
      include_entities?: boolean;
      include_relations?: boolean;
    };

    // target_dirのパストラバーサル検証
    if (typeof target_dir === 'string' && hasPathTraversal(target_dir)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'target_dir contains path traversal segments', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // sinceの日時バリデーション
    if (since !== undefined) {
      if (typeof since !== 'string' || !Number.isFinite(Date.parse(since))) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'since must be a valid ISO 8601 datetime string', reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    // Push実行オプションの構築
    const options: PushOptions = {
      basePath: process.cwd(),
      ...(target_dir && { targetDir: target_dir }),
      ...(scope_filter && { scopeFilter: scope_filter as Scope[] }),
      ...(boundary_filter && { boundaryFilter: boundary_filter as BoundaryClass[] }),
      ...(since && { since: new Date(since) }),
      ...(include_entities !== undefined && { includeEntities: include_entities }),
      ...(include_relations !== undefined && { includeRelations: include_relations }),
    };

    // Push実行
    const result = await executePush(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_push',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_PUSH_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_push',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      exported: result.right.exported,
      target_dir: result.right.targetDir,
      manifest_updated: result.right.manifestUpdated,
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_push',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_PUSH_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

/**
 * Sync Pull: .pce-shared/からローカルDBへインポート
 */
export async function handleSyncPull(args: Record<string, unknown>): Promise<ToolResult> {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以降で利用可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 引数の取得
    const { source_dir, scope_filter, boundary_filter, dry_run, since } = args as {
      source_dir?: string;
      scope_filter?: string[];
      boundary_filter?: string[];
      dry_run?: boolean;
      since?: string; // Phase 2: 増分インポート用ISO8601日時
    };

    // source_dirのパストラバーサル検証
    if (typeof source_dir === 'string' && hasPathTraversal(source_dir)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'source_dir contains path traversal segments', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // sinceの日時バリデーション
    if (since !== undefined) {
      if (typeof since !== 'string' || !Number.isFinite(Date.parse(since))) {
        return createToolResult(
          { ...err('VALIDATION_ERROR', 'since must be a valid ISO 8601 datetime string', reqId), trace_id: traceId },
          { isError: true }
        );
      }
    }

    // Pull実行オプションの構築
    const options: PullOptions = {
      basePath: process.cwd(),
      ...(source_dir && { sourceDir: source_dir }),
      ...(scope_filter && { scopeFilter: scope_filter as Scope[] }),
      ...(boundary_filter && { boundaryFilter: boundary_filter as BoundaryClass[] }),
      ...(dry_run !== undefined && { dryRun: dry_run }),
      ...(since && { since: new Date(since) }),
    };

    // Pull実行
    const result = await executePull(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_pull',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_PULL_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 新しいClaimがインポートされた場合は状態遷移
    const totalNewClaims = result.right.imported.claims.new;

    if (totalNewClaims > 0 && !result.right.dryRun) {
      // totalNewClaims回分、状態遷移を行う（claimCountを増加させるため）
      for (let i = 0; i < totalNewClaims; i++) {
        transitionToHasClaims(true);
      }
    }

    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_pull',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      imported: {
        claims: {
          new: result.right.imported.claims.new,
          skipped_duplicate: result.right.imported.claims.skippedDuplicate,
          upgraded_boundary: result.right.imported.claims.upgradedBoundary,
          skipped_by_since: result.right.imported.claims.skippedBySince, // Phase 2
        },
        entities: {
          new: result.right.imported.entities.new,
          skipped_duplicate: result.right.imported.entities.skippedDuplicate,
        },
        relations: {
          new: result.right.imported.relations.new,
          skipped_duplicate: result.right.imported.relations.skippedDuplicate,
        },
      },
      validation_errors: result.right.validationErrors,
      dry_run: result.right.dryRun,
      manifest_updated: result.right.manifestUpdated, // Phase 2
      // Phase 3: 衝突検出レポート
      conflicts: {
        total: result.right.conflicts.conflicts.length,
        auto_resolved: result.right.conflicts.autoResolved,
        skipped: result.right.conflicts.skipped,
        details: result.right.conflicts.conflicts.slice(0, 10), // 最初の10件のみ
      },
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_pull',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_PULL_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

/**
 * Sync Status Handler (Phase 2)
 * 同期ディレクトリの状態を確認
 */
export async function handleSyncStatus(args: Record<string, unknown>): Promise<ToolResult> {
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();

  try {
    // 状態検証（PolicyApplied以上で実行可能）
    if (!canDoQuery()) {
      const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // レート制限チェック
    if (!(await checkAndConsume('tool'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 引数の取得と検証
    const { target_dir } = args as { target_dir?: unknown };

    // 型検証: target_dirはstring | undefinedのみ許可
    if (target_dir !== undefined && typeof target_dir !== 'string') {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'target_dir must be a string', reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // Statusオプション構築
    const options: StatusOptions = {
      basePath: process.cwd(),
      ...(typeof target_dir === 'string' && { targetDir: target_dir }),
    };

    // Status実行
    const result = await executeStatus(options);

    if (E.isLeft(result)) {
      await appendLog({
        id: `log_${reqId}`,
        op: 'sync_status',
        ok: false,
        req: reqId,
        trace: traceId,
        policy_version: getPolicyVersion(),
      });
      return createToolResult(
        { ...err('SYNC_STATUS_FAILED', result.left.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    // 成功時のログ記録
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_status',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });

    return createToolResult({
      exists: result.right.exists,
      manifest: result.right.manifest,
      files: result.right.files,
      validation: result.right.validation,
      target_dir: result.right.targetDir,
      policy_version: result.right.policyVersion,
      state: getStateType(),
      request_id: reqId,
      trace_id: traceId,
    });
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'sync_status',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('SYNC_STATUS_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

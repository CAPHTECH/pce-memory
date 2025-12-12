#!/usr/bin/env node
/**
 * CLI Sync Commands (Issue #18 Phase 3)
 *
 * Git hooksから呼び出すためのコマンドラインインターフェース
 *
 * Usage:
 *   pce-memory sync push [--db <path>] [--target-dir .pce-shared]
 *   pce-memory sync pull [--db <path>] [--source-dir .pce-shared] [--dry-run]
 *   pce-memory sync status [--db <path>] [--target-dir .pce-shared]
 */
import * as E from 'fp-ts/Either';
import * as path from 'node:path';
import * as os from 'node:os';

import { initDb, initSchema } from '../db/connection.js';
import { initRateState } from '../store/rate.js';
import { initMemoryState } from '../state/memoryState.js';
import { executePush, type PushOptions } from '../sync/push.js';
import { executePull, type PullOptions } from '../sync/pull.js';
import { executeStatus, type StatusOptions } from '../sync/status.js';
import type { Scope, BoundaryClass } from '../sync/schemas.js';

/**
 * 有効なスコープ値
 */
const VALID_SCOPES: readonly Scope[] = ['session', 'project', 'principle'];

/**
 * 有効な境界クラス値
 */
const VALID_BOUNDARIES: readonly BoundaryClass[] = ['public', 'internal', 'pii', 'secret'];

/**
 * スコープフィルタを検証してパース
 * @returns パースされたスコープ配列、または無効な場合はnull
 */
function parseScopeFilter(value: string): Scope[] | null {
  const scopes = value.split(',').map((s) => s.trim());
  const invalid = scopes.filter((s) => !VALID_SCOPES.includes(s as Scope));
  if (invalid.length > 0) {
    console.error(`[pce-sync] Invalid scope(s): ${invalid.join(', ')}`);
    console.error(`  Valid values: ${VALID_SCOPES.join(', ')}`);
    return null;
  }
  return scopes as Scope[];
}

/**
 * 境界クラスフィルタを検証してパース
 * @returns パースされた境界クラス配列、または無効な場合はnull
 */
function parseBoundaryFilter(value: string): BoundaryClass[] | null {
  const boundaries = value.split(',').map((s) => s.trim());
  const invalid = boundaries.filter((s) => !VALID_BOUNDARIES.includes(s as BoundaryClass));
  if (invalid.length > 0) {
    console.error(`[pce-sync] Invalid boundary class(es): ${invalid.join(', ')}`);
    console.error(`  Valid values: ${VALID_BOUNDARIES.join(', ')}`);
    return null;
  }
  return boundaries as BoundaryClass[];
}

/**
 * 日付文字列を検証してパース
 * @returns パースされたDate、または無効な場合はnull
 */
function parseDateOption(value: string): Date | null {
  const parsed = new Date(value);
  if (isNaN(parsed.getTime())) {
    console.error(`[pce-sync] Invalid date format: ${value}`);
    console.error(`  Expected: ISO 8601 format (e.g., 2025-01-01T00:00:00Z)`);
    return null;
  }
  return parsed;
}

/**
 * グローバルオプション（--db）を抽出し、残りの引数を返す
 * --db オプションが指定された場合、環境変数 PCE_DB を設定する
 */
function extractGlobalOptions(args: string[]): string[] {
  const remaining: string[] = [];

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === undefined) continue;
    const nextArg = args[i + 1];
    if ((arg === '--db' || arg === '-d') && nextArg !== undefined) {
      // DBパスを環境変数に設定（initDbで使用される）
      process.env['PCE_DB'] = expandTilde(nextArg);
      i++;
    } else {
      remaining.push(arg);
    }
  }

  return remaining;
}

/**
 * DB初期化（sync操作に必要な最小限の初期化）
 */
async function initForSync(): Promise<boolean> {
  try {
    await initDb();
    await initSchema();
    await initRateState();

    const initResult = await initMemoryState()();
    if (E.isLeft(initResult)) {
      console.error(`[pce-sync] State initialization failed: ${initResult.left.message}`);
      // 初期化失敗でも続行（policy未適用の可能性）
    }

    return true;
  } catch (err) {
    console.error(`[pce-sync] DB initialization failed: ${(err as Error).message}`);
    return false;
  }
}

/**
 * パス内の ~ をホームディレクトリに展開
 */
function expandTilde(filePath: string): string {
  if (filePath.startsWith('~/')) {
    return path.join(os.homedir(), filePath.slice(2));
  }
  if (filePath === '~') {
    return os.homedir();
  }
  return filePath;
}

/**
 * sync push コマンド
 */
async function handlePush(args: string[]): Promise<number> {
  // 引数パース
  let targetDir: string | undefined;
  let scopeFilter: Scope[] | undefined;
  let boundaryFilter: BoundaryClass[] | undefined;
  let since: Date | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    const nextArg = args[i + 1];
    if (arg === '--target-dir' && nextArg !== undefined) {
      targetDir = expandTilde(nextArg);
      i++;
    } else if (arg === '--scope-filter' && nextArg !== undefined) {
      const parsed = parseScopeFilter(nextArg);
      if (parsed === null) return 1;
      scopeFilter = parsed;
      i++;
    } else if (arg === '--boundary-filter' && nextArg !== undefined) {
      const parsed = parseBoundaryFilter(nextArg);
      if (parsed === null) return 1;
      boundaryFilter = parsed;
      i++;
    } else if (arg === '--since' && nextArg !== undefined) {
      const parsed = parseDateOption(nextArg);
      if (parsed === null) return 1;
      since = parsed;
      i++;
    }
  }

  // DB初期化
  if (!(await initForSync())) {
    return 1;
  }

  // Push実行
  const options: PushOptions = {
    basePath: process.cwd(),
    ...(targetDir && { targetDir }),
    ...(scopeFilter && { scopeFilter }),
    ...(boundaryFilter && { boundaryFilter }),
    ...(since && { since }),
  };

  const result = await executePush(options);

  if (E.isLeft(result)) {
    console.error(`[pce-sync] Push failed: ${result.left.message}`);
    return 1;
  }

  console.log(
    `[pce-sync] Exported: ${result.right.exported.claims} claims, ${result.right.exported.entities} entities, ${result.right.exported.relations} relations`
  );

  return 0;
}

/**
 * sync pull コマンド
 */
async function handlePull(args: string[]): Promise<number> {
  // 引数パース
  let sourceDir: string | undefined;
  let scopeFilter: Scope[] | undefined;
  let boundaryFilter: BoundaryClass[] | undefined;
  let dryRun = false;
  let since: Date | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    const nextArg = args[i + 1];
    if (arg === '--source-dir' && nextArg !== undefined) {
      sourceDir = expandTilde(nextArg);
      i++;
    } else if (arg === '--scope-filter' && nextArg !== undefined) {
      const parsed = parseScopeFilter(nextArg);
      if (parsed === null) return 1;
      scopeFilter = parsed;
      i++;
    } else if (arg === '--boundary-filter' && nextArg !== undefined) {
      const parsed = parseBoundaryFilter(nextArg);
      if (parsed === null) return 1;
      boundaryFilter = parsed;
      i++;
    } else if (arg === '--dry-run') {
      dryRun = true;
    } else if (arg === '--since' && nextArg !== undefined) {
      const parsed = parseDateOption(nextArg);
      if (parsed === null) return 1;
      since = parsed;
      i++;
    }
  }

  // DB初期化
  if (!(await initForSync())) {
    return 1;
  }

  // Pull実行
  const options: PullOptions = {
    basePath: process.cwd(),
    ...(sourceDir && { sourceDir }),
    ...(scopeFilter && { scopeFilter }),
    ...(boundaryFilter && { boundaryFilter }),
    dryRun,
    ...(since && { since }),
  };

  const result = await executePull(options);

  if (E.isLeft(result)) {
    console.error(`[pce-sync] Pull failed: ${result.left.message}`);
    return 1;
  }

  const { imported, conflicts } = result.right;

  console.log(
    `[pce-sync] Imported: ${imported.claims.new} claims (new), ${imported.entities.new} entities, ${imported.relations.new} relations`
  );

  if (conflicts.conflicts.length > 0) {
    console.log(`[pce-sync] Conflicts:`);
    console.log(`  - Auto-resolved: ${conflicts.autoResolved}`);
    console.log(`  - Skipped: ${conflicts.skipped}`);

    // 詳細を表示（最初の5件）
    for (const conflict of conflicts.conflicts.slice(0, 5)) {
      console.log(`  - [${conflict.type}] ${conflict.message}`);
    }

    if (conflicts.conflicts.length > 5) {
      console.log(`  ... and ${conflicts.conflicts.length - 5} more`);
    }
  }

  if (dryRun) {
    console.log('[pce-sync] (dry-run mode - no changes were made)');
  }

  return 0;
}

/**
 * sync status コマンド
 */
async function handleStatus(args: string[]): Promise<number> {
  // 引数パース
  let targetDir: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    const nextArg = args[i + 1];
    if (arg === '--target-dir' && nextArg !== undefined) {
      targetDir = expandTilde(nextArg);
      i++;
    }
  }

  // Status実行（DB初期化不要）
  const options: StatusOptions = {
    basePath: process.cwd(),
    ...(targetDir && { targetDir }),
  };

  const result = await executeStatus(options);

  if (E.isLeft(result)) {
    console.error(`[pce-sync] Status check failed: ${result.left.message}`);
    return 1;
  }

  const status = result.right;

  console.log(`[pce-sync] Sync directory: ${status.targetDir}`);
  console.log(`  Exists: ${status.exists ? 'yes' : 'no'}`);

  if (status.exists) {
    console.log(`  Files:`);
    console.log(`    - Claims: ${status.files.claims}`);
    console.log(`    - Entities: ${status.files.entities}`);
    console.log(`    - Relations: ${status.files.relations}`);

    if (status.manifest) {
      console.log(`  Manifest:`);
      console.log(`    - Version: ${status.manifest.version}`);
      console.log(`    - PCE Memory Version: ${status.manifest.pce_memory_version}`);
      console.log(`    - Last Push: ${status.manifest.last_push_at}`);
      if (status.manifest.last_pull_at) {
        console.log(`    - Last Pull: ${status.manifest.last_pull_at}`);
      }
    }

    if (status.validation.errors.length > 0) {
      console.log(`  Validation Errors: ${status.validation.errors.length}`);
      for (const error of status.validation.errors.slice(0, 3)) {
        console.log(`    - ${error}`);
      }
    }
  }

  return 0;
}

/**
 * sync コマンドのヘルプを表示
 */
function showHelp(): void {
  console.log(`
	pce-memory sync - Git-based CRDT sync commands

	Usage: pce-memory sync <command> [options]

Commands:
  push      Export local DB to .pce-shared/
  pull      Import from .pce-shared/ to local DB
  status    Show sync directory status

	Global options:
	  -d, --db <path>          DuckDB file path (default: $PCE_DB or :memory:)

	Notes:
	  - If --target-dir/--source-dir is omitted and you're inside a Git repo,
	    .pce-shared is resolved at the Git repository root.

	Options for push:
	  --target-dir <path>      Target directory (default: .pce-shared)
	  --scope-filter <scopes>  Comma-separated scopes (e.g., project,principle)
	  --boundary-filter <bc>   Comma-separated boundary classes (e.g., public,internal)
	  --since <ISO8601>        Export only items after this date

	Options for pull:
	  --source-dir <path>      Source directory (default: .pce-shared)
	  --scope-filter <scopes>  Comma-separated scopes
	  --boundary-filter <bc>   Comma-separated boundary classes
	  --dry-run                Preview changes without importing
	  --since <ISO8601>        Import only items after this date

Options for status:
  --target-dir <path>      Target directory (default: .pce-shared)

Examples:
  pce-memory sync --db ~/my.pce.db push
  pce-memory sync pull --dry-run
  pce-memory sync status
`);
}

/**
 * sync コマンドのエントリポイント
 */
export async function runSyncCommand(args: string[]): Promise<number> {
  // グローバルオプション（--db）を抽出
  const remainingArgs = extractGlobalOptions(args);
  const [subcommand, ...subArgs] = remainingArgs;

  switch (subcommand) {
    case 'push':
      return handlePush(subArgs);
    case 'pull':
      return handlePull(subArgs);
    case 'status':
      return handleStatus(subArgs);
    case '--help':
    case '-h':
    case undefined:
      showHelp();
      return 0;
    default:
      console.error(`[pce-sync] Unknown subcommand: ${subcommand}`);
      showHelp();
      return 1;
  }
}

// Note: 直接実行コードは削除済み
// sync CLIは proxy.ts の handleSubcommand() 経由で呼び出される
// バンドル後は import.meta.url が共有されるため、直接実行チェックは機能しない

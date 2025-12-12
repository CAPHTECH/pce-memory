#!/usr/bin/env node
/**
 * CLI Sync Commands (Issue #18 Phase 3)
 *
 * Git hooksから呼び出すためのコマンドラインインターフェース
 *
 * Usage:
 *   pce-memory sync push [--target-dir .pce-shared]
 *   pce-memory sync pull [--source-dir .pce-shared] [--dry-run]
 *   pce-memory sync status [--target-dir .pce-shared]
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
  let targetDir = '.pce-shared';
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
      scopeFilter = nextArg.split(',') as Scope[];
      i++;
    } else if (arg === '--boundary-filter' && nextArg !== undefined) {
      boundaryFilter = nextArg.split(',') as BoundaryClass[];
      i++;
    } else if (arg === '--since' && nextArg !== undefined) {
      since = new Date(nextArg);
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
    targetDir,
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
  let sourceDir = '.pce-shared';
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
      scopeFilter = nextArg.split(',') as Scope[];
      i++;
    } else if (arg === '--boundary-filter' && nextArg !== undefined) {
      boundaryFilter = nextArg.split(',') as BoundaryClass[];
      i++;
    } else if (arg === '--dry-run') {
      dryRun = true;
    } else if (arg === '--since' && nextArg !== undefined) {
      since = new Date(nextArg);
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
    sourceDir,
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

  console.log(`[pce-sync] Imported: ${imported.claims.new} claims (new), ${imported.entities.new} entities, ${imported.relations.new} relations`);

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
  let targetDir = '.pce-shared';

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
    targetDir,
  };

  const result = await executeStatus(options);

  if (E.isLeft(result)) {
    console.error(`[pce-sync] Status check failed: ${result.left.message}`);
    return 1;
  }

  const status = result.right;

  console.log(`[pce-sync] Sync directory: ${path.join(process.cwd(), targetDir)}`);
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
  pce-memory sync push
  pce-memory sync pull --dry-run
  pce-memory sync status
`);
}

/**
 * sync コマンドのエントリポイント
 */
export async function runSyncCommand(args: string[]): Promise<number> {
  const [subcommand, ...subArgs] = args;

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

// 直接実行された場合
const scriptPath = process.argv[1];
if (scriptPath && import.meta.url.endsWith(scriptPath.replace(/^file:\/\//, ''))) {
  const args = process.argv.slice(2);
  runSyncCommand(args)
    .then((code) => process.exit(code))
    .catch((err) => {
      console.error(`[pce-sync] Unhandled error: ${err}`);
      process.exit(1);
    });
}

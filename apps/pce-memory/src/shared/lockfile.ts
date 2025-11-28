/**
 * Lockfile Management
 *
 * アトミックなファイル作成（wx flag）で排他制御を実現。
 * stale lock（プロセス終了後の残骸）を自動検出・削除。
 *
 * @see kiri/src/shared/utils/lockfile.ts
 */

import { existsSync, readFileSync, unlinkSync, writeFileSync } from 'node:fs';

/**
 * ロックファイルエラー
 */
export class LockfileError extends Error {
  constructor(
    message: string,
    public readonly lockfilePath: string,
    public readonly ownerPid?: number
  ) {
    super(message);
    this.name = 'LockfileError';
  }
}

/**
 * 指定PIDのプロセスが実行中かチェック
 *
 * @param pid - チェック対象のプロセスID
 * @returns プロセスが存在する場合true
 */
function isProcessRunning(pid: number): boolean {
  try {
    // シグナル0はプロセスの存在チェック（実際には何もしない）
    process.kill(pid, 0);
    return true;
  } catch {
    // ESRCH: プロセスが存在しない
    return false;
  }
}

/**
 * ロックファイルをアトミックに取得
 *
 * 既存ロックがあるが所有プロセスが死んでいる場合、
 * stale lockとして削除して再取得を試みる。
 *
 * @param lockfilePath - ロックファイルのパス
 * @throws {LockfileError} ロックが既に他のプロセスに保持されている場合
 */
export function acquireLock(lockfilePath: string): void {
  try {
    // アトミックな排他的作成（wx flag）
    writeFileSync(lockfilePath, String(process.pid), { flag: 'wx' });
  } catch (error) {
    const err = error as NodeJS.ErrnoException;

    if (err.code === 'EEXIST') {
      // ロックファイルが既に存在 → stale checkを実行
      try {
        const existingPidStr = readFileSync(lockfilePath, 'utf8');
        const existingPid = parseInt(existingPidStr, 10);

        if (!isNaN(existingPid) && !isProcessRunning(existingPid)) {
          // Stale lock検出 - 再確認してから削除（TOCTOU対策）
          console.error(`[Lockfile] Removing stale lock file (PID ${existingPid} not running)`);

          if (existsSync(lockfilePath)) {
            const recheckPidStr = readFileSync(lockfilePath, 'utf8');
            const recheckPid = parseInt(recheckPidStr, 10);

            // PIDが一致し、プロセスがまだ死んでいる場合のみ削除
            if (!isNaN(recheckPid) && recheckPid === existingPid && !isProcessRunning(recheckPid)) {
              unlinkSync(lockfilePath);

              // 再取得を試みる
              writeFileSync(lockfilePath, String(process.pid), { flag: 'wx' });
              return;
            }
          }

          // ロックファイルが変更された → レース発生
          throw new LockfileError(
            `Lock file changed during stale check. Another process may be active.`,
            lockfilePath,
            existingPid
          );
        }

        // ロックは実行中のプロセスが保持
        throw new LockfileError(
          `Lock file already exists. Another process is active.`,
          lockfilePath,
          existingPid
        );
      } catch (lockError) {
        if (lockError instanceof LockfileError) {
          throw lockError;
        }
        // PID読み取り失敗 → 安全のためアクティブとみなす
        throw new LockfileError(
          `Lock file already exists. Another process may be active.`,
          lockfilePath
        );
      }
    }
    throw err;
  }
}

/**
 * ロックファイルを解放
 *
 * ファイルが存在しない場合は静かに成功（冪等）。
 *
 * @param lockfilePath - ロックファイルのパス
 */
export function releaseLock(lockfilePath: string): void {
  try {
    if (existsSync(lockfilePath)) {
      unlinkSync(lockfilePath);
    }
  } catch {
    // クリーンアップ時のエラーは無視
  }
}

/**
 * ロックファイルが存在するかチェック
 *
 * @param lockfilePath - ロックファイルのパス
 * @returns ロックファイルが存在する場合true
 */
export function isLocked(lockfilePath: string): boolean {
  return existsSync(lockfilePath);
}

/**
 * ロックファイルの所有プロセスIDを取得
 *
 * @param lockfilePath - ロックファイルのパス
 * @returns 所有プロセスのPID、またはnull
 */
export function getLockOwner(lockfilePath: string): number | null {
  try {
    if (existsSync(lockfilePath)) {
      const pidStr = readFileSync(lockfilePath, 'utf8');
      const pid = parseInt(pidStr, 10);
      return isNaN(pid) ? null : pid;
    }
  } catch {
    return null;
  }
  return null;
}

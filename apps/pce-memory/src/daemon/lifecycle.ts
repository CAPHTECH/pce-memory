/**
 * Daemon Lifecycle Management
 *
 * PIDファイル作成、アイドルタイムアウト、ヘルスチェック、
 * グレースフルシャットダウンを管理する。
 *
 * @see kiri/src/daemon/lifecycle.ts
 */

import * as fs from 'fs/promises';
import { acquireLock, releaseLock, LockfileError } from '../shared/lockfile.js';

/**
 * デーモンライフサイクル管理クラス
 */
export class DaemonLifecycle {
  private readonly pidFilePath: string;
  private readonly startupLockPath: string;
  private readonly logFilePath: string;
  private idleTimer: NodeJS.Timeout | null = null;
  private activeConnections = 0;
  private shutdownCallback?: () => Promise<void>;
  private readonly maxLogSizeBytes: number = 10 * 1024 * 1024; // 10MB
  private readonly maxLogBackups: number = 3;

  constructor(
    databasePath: string,
    private readonly idleTimeoutMinutes: number = 5
  ) {
    this.pidFilePath = `${databasePath}.daemon.pid`;
    this.startupLockPath = `${databasePath}.daemon.starting`;
    this.logFilePath = `${databasePath}.daemon.log`;
  }

  /**
   * PIDファイルパスを取得
   */
  getPidFilePath(): string {
    return this.pidFilePath;
  }

  /**
   * スタートアップロックファイルパスを取得
   */
  getStartupLockPath(): string {
    return this.startupLockPath;
  }

  /**
   * ログファイルパスを取得
   */
  getLogFilePath(): string {
    return this.logFilePath;
  }

  /**
   * スタートアップロックを取得（排他的作成 + stale lock検出）
   *
   * lockfile.tsに委譲することで、以下の機能を提供:
   * - アトミックなファイル作成（wx flag）
   * - stale lock検出（PID生存確認）
   * - TOCTOU脆弱性対策（ダブルチェック）
   *
   * @remarks 内部的に同期APIを使用するが、起動時1回のみの呼び出しなので許容。
   * @returns ロック取得に成功した場合はtrue、他のプロセスが既にロック中の場合はfalse
   */
  async acquireStartupLock(): Promise<boolean> {
    try {
      acquireLock(this.startupLockPath);
      return true;
    } catch (err) {
      if (err instanceof LockfileError) {
        // 他のプロセスがロックを保持中（stale lockは自動検出・削除済み）
        return false;
      }
      throw err;
    }
  }

  /**
   * スタートアップロックを解放
   *
   * lockfile.tsのreleaseLock()に委譲。
   * ファイルが存在しない場合は静かに成功（冪等）。
   * 解放失敗時はログ出力するが、例外はスローしない（シャットダウン継続を優先）。
   *
   * @remarks 内部的に同期APIを使用するが、シャットダウン時1回のみの呼び出しなので許容。
   */
  async releaseStartupLock(): Promise<void> {
    try {
      releaseLock(this.startupLockPath);
    } catch (err) {
      // シャットダウン継続を優先し、エラーはログのみ
      console.error(`[Daemon] Failed to release startup lock: ${err}`);
    }
  }

  /**
   * PIDファイルを作成
   */
  async createPidFile(): Promise<void> {
    await fs.writeFile(this.pidFilePath, String(process.pid), 'utf-8');
  }

  /**
   * PIDファイルを削除
   */
  async removePidFile(): Promise<void> {
    try {
      await fs.unlink(this.pidFilePath);
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== 'ENOENT') {
        console.error(`[Daemon] Failed to remove PID file: ${err}`);
      }
    }
  }

  /**
   * デーモンが実行中かチェック
   *
   * @returns デーモンが実行中の場合はPID、それ以外はnull
   */
  async checkRunning(): Promise<number | null> {
    try {
      const pidStr = await fs.readFile(this.pidFilePath, 'utf-8');
      const pid = parseInt(pidStr.trim(), 10);

      try {
        process.kill(pid, 0); // シグナル0は存在チェック
        return pid;
      } catch {
        // プロセスが存在しない
        return null;
      }
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code === 'ENOENT') {
        return null;
      }
      throw err;
    }
  }

  /**
   * アクティブ接続数を増やす
   */
  incrementConnections(): void {
    this.activeConnections++;
    this.resetIdleTimer();
  }

  /**
   * アクティブ接続数を減らす
   */
  decrementConnections(): void {
    this.activeConnections = Math.max(0, this.activeConnections - 1);
    if (this.activeConnections === 0) {
      this.startIdleTimer();
    }
  }

  /**
   * 現在のアクティブ接続数を取得
   */
  getActiveConnections(): number {
    return this.activeConnections;
  }

  /**
   * シャットダウンコールバックを登録
   */
  onShutdown(callback: () => Promise<void>): void {
    this.shutdownCallback = callback;
  }

  /**
   * アイドルタイマーをリセット
   */
  private resetIdleTimer(): void {
    if (this.idleTimer) {
      clearTimeout(this.idleTimer);
      this.idleTimer = null;
    }
  }

  /**
   * アイドルタイマーを開始
   */
  private startIdleTimer(): void {
    if (this.idleTimeoutMinutes === 0) {
      return; // タイムアウト無効
    }

    this.resetIdleTimer();
    this.idleTimer = setTimeout(
      async () => {
        if (this.activeConnections === 0) {
          await this.log(
            `Idle timeout (${this.idleTimeoutMinutes} minutes) reached. Shutting down...`
          );
          console.error(
            `[Daemon] Idle timeout (${this.idleTimeoutMinutes} minutes) reached. Shutting down...`
          );
          if (this.shutdownCallback) {
            await this.shutdownCallback();
          }
          process.exit(0);
        }
      },
      this.idleTimeoutMinutes * 60 * 1000
    );
  }

  /**
   * グレースフルシャットダウンを設定
   */
  setupGracefulShutdown(): void {
    const shutdown = async (signal: string) => {
      console.error(`[Daemon] Received ${signal}. Shutting down gracefully...`);
      await this.log(`Received ${signal}. Shutting down gracefully...`);

      this.resetIdleTimer();

      if (this.shutdownCallback) {
        await this.shutdownCallback();
      }

      await this.removePidFile();
      await this.releaseStartupLock();

      process.exit(0);
    };

    process.on('SIGTERM', () => shutdown('SIGTERM'));
    process.on('SIGINT', () => shutdown('SIGINT'));
  }

  /**
   * ログファイルをローテーション
   */
  private async rotateLogIfNeeded(): Promise<void> {
    try {
      const stats = await fs.stat(this.logFilePath);
      if (stats.size < this.maxLogSizeBytes) {
        return;
      }

      // 既存バックアップをシフト
      for (let i = this.maxLogBackups; i > 0; i--) {
        const oldBackup = `${this.logFilePath}.${i}`;
        const newBackup = `${this.logFilePath}.${i + 1}`;
        try {
          await fs.access(oldBackup);
          if (i === this.maxLogBackups) {
            await fs.unlink(oldBackup);
          } else {
            await fs.rename(oldBackup, newBackup);
          }
        } catch {
          // ファイルが存在しない場合は無視
        }
      }

      await fs.rename(this.logFilePath, `${this.logFilePath}.1`);
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== 'ENOENT') {
        console.error(`[Daemon] Failed to rotate log file: ${err}`);
      }
    }
  }

  /**
   * ログファイルにメッセージを書き込む
   */
  async log(message: string): Promise<void> {
    this.rotateLogIfNeeded().catch((err) => {
      console.error(`[Daemon] Log rotation failed: ${err}`);
    });

    const timestamp = new Date().toISOString();
    const logMessage = `${timestamp} ${message}\n`;
    try {
      await fs.appendFile(this.logFilePath, logMessage, 'utf-8');
    } catch (err) {
      console.error(`[Daemon] Failed to write to log file: ${err}`);
    }
  }
}

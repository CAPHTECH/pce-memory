/**
 * Daemon Starter Utility
 *
 * デーモンプロセスをデタッチモードで起動し、準備完了を待つ。
 *
 * @see kiri/src/client/start-daemon.ts
 */

import { spawn } from "child_process";
import * as fs from "fs/promises";
import * as net from "net";
import * as path from "path";
import { fileURLToPath } from "url";

import { getSocketPath } from "../shared/socket.js";

/**
 * デーモン起動オプション
 */
export interface StartDaemonOptions {
  databasePath: string;
  socketPath?: string;
  idleTimeoutMinutes?: number;
  readyTimeoutMs?: number;
}

/**
 * デーモンが実行中かチェック
 *
 * PIDファイルの存在とプロセスの存在、ソケット接続可能性を確認
 */
export async function isDaemonRunning(databasePath: string): Promise<boolean> {
  const pidFilePath = `${databasePath}.daemon.pid`;
  const socketPath = getSocketPath(databasePath);

  try {
    // PIDファイルが存在するかチェック
    const pidStr = await fs.readFile(pidFilePath, "utf-8");
    const pid = parseInt(pidStr.trim(), 10);

    // 不正なPID値のチェック
    if (isNaN(pid) || pid <= 0) {
      console.error("[StartDaemon] Invalid PID in PID file, treating as stale");
      return false;
    }

    // プロセスが実際に存在するかチェック
    try {
      process.kill(pid, 0);
    } catch {
      console.error("[StartDaemon] Stale PID file detected");
      return false;
    }

    // ソケットにpingヘルスチェックを実行
    try {
      const socket = net.connect(socketPath);

      const healthCheck = await new Promise<boolean>((resolve, reject) => {
        const timeout = setTimeout(() => {
          socket.destroy();
          reject(new Error("Health check timeout"));
        }, 2000);

        let responseReceived = false;

        socket.on("connect", () => {
          const pingRequest = {
            jsonrpc: "2.0",
            id: 1,
            method: "ping",
          };
          socket.write(JSON.stringify(pingRequest) + "\n");
        });

        socket.on("data", (data) => {
          if (responseReceived) return;

          try {
            const response = JSON.parse(data.toString().trim());
            if (response.result && response.result.status === "ok") {
              responseReceived = true;
              clearTimeout(timeout);
              socket.end();
              resolve(true);
            } else {
              clearTimeout(timeout);
              socket.destroy();
              reject(new Error("Invalid ping response"));
            }
          } catch {
            clearTimeout(timeout);
            socket.destroy();
            reject(new Error("Failed to parse health check response"));
          }
        });

        socket.on("error", (err) => {
          clearTimeout(timeout);
          reject(err);
        });
      });

      return healthCheck;
    } catch (err) {
      console.error(
        `[StartDaemon] Daemon health check failed: ${err instanceof Error ? err.message : String(err)}`
      );
      return false;
    }
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") {
      return false;
    }
    throw err;
  }
}

/**
 * デーモンプロセスを停止
 */
export async function stopDaemon(databasePath: string): Promise<void> {
  const pidFilePath = `${databasePath}.daemon.pid`;
  const startupLockPath = `${databasePath}.daemon.starting`;

  try {
    const pidStr = await fs.readFile(pidFilePath, "utf-8");
    const pid = parseInt(pidStr.trim(), 10);

    // 不正なPID値のチェック
    if (isNaN(pid) || pid <= 0) {
      console.error("[StopDaemon] Invalid PID in PID file, cleaning up files");
      await fs.unlink(pidFilePath).catch(() => {});
      await fs.unlink(startupLockPath).catch(() => {});
      return;
    }

    try {
      process.kill(pid, 0);
    } catch {
      console.error("[StopDaemon] Process not found, cleaning up files");
      await fs.unlink(pidFilePath).catch(() => {});
      await fs.unlink(startupLockPath).catch(() => {});
      return;
    }

    console.error(`[StopDaemon] Stopping daemon (PID: ${pid})...`);
    process.kill(pid, "SIGTERM");

    // 最大5秒待機
    for (let i = 0; i < 50; i++) {
      await new Promise((resolve) => setTimeout(resolve, 100));
      try {
        process.kill(pid, 0);
      } catch {
        console.error("[StopDaemon] Daemon stopped gracefully");
        await fs.unlink(pidFilePath).catch(() => {});
        await fs.unlink(startupLockPath).catch(() => {});
        return;
      }
    }

    // タイムアウト → 強制終了
    console.error("[StopDaemon] Force killing daemon...");
    process.kill(pid, "SIGKILL");
    await fs.unlink(pidFilePath).catch(() => {});
    await fs.unlink(startupLockPath).catch(() => {});
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ENOENT") {
      return;
    }
    throw err;
  }
}

/**
 * デーモンプロセスを起動
 */
export async function startDaemon(options: StartDaemonOptions): Promise<void> {
  const {
    databasePath,
    socketPath: customSocketPath,
    idleTimeoutMinutes,
    readyTimeoutMs,
  } = options;

  const socketPath = customSocketPath || getSocketPath(databasePath);

  // デーモン実行ファイルのパスを解決
  const __filename = fileURLToPath(import.meta.url);
  const __dirname = path.dirname(__filename);
  const daemonScriptPath = path.resolve(__dirname, "../daemon/daemon.js");

  // デーモン起動引数
  const args = ["--db", databasePath, "--socket-path", socketPath];

  if (idleTimeoutMinutes !== undefined) {
    args.push("--daemon-timeout", String(idleTimeoutMinutes));
  }

  // データベースの親ディレクトリを自動作成
  const dbDir = path.dirname(databasePath);
  await fs.mkdir(dbDir, { recursive: true });

  // デーモンログファイル
  const logFilePath = `${databasePath}.daemon.log`;
  const logFile = await fs.open(logFilePath, "a");

  // デタッチモードでデーモンを起動
  const daemon = spawn(process.execPath, [daemonScriptPath, ...args], {
    detached: true,
    stdio: ["ignore", logFile.fd, logFile.fd],
  });

  daemon.unref();

  console.error(`[StartDaemon] Spawned daemon process (PID: ${daemon.pid})`);
  console.error(`[StartDaemon] Daemon log: ${logFilePath}`);

  // ソケットが準備完了するまで待つ
  const effectiveTimeoutMs = readyTimeoutMs ?? 60_000; // デフォルト60秒
  const pollIntervalMs = 500;
  const maxAttempts = Math.max(1, Math.ceil(effectiveTimeoutMs / pollIntervalMs));

  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    try {
      const socket = net.connect(socketPath);
      await new Promise<void>((resolve, reject) => {
        const timeout = setTimeout(() => {
          socket.destroy();
          reject(new Error("Socket connection timeout"));
        }, pollIntervalMs);

        socket.on("connect", () => {
          clearTimeout(timeout);
          socket.end();
          resolve();
        });

        socket.on("error", (err) => {
          clearTimeout(timeout);
          reject(err);
        });
      });

      console.error("[StartDaemon] Daemon is ready");
      await logFile.close();
      return;
    } catch {
      await new Promise((resolve) => setTimeout(resolve, pollIntervalMs));
    }
  }

  await logFile.close();
  throw new Error(
    `Daemon did not become ready within ${Math.round(effectiveTimeoutMs / 1000)} seconds. Check log: ${logFilePath}`
  );
}

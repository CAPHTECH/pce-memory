#!/usr/bin/env node
/**
 * PCE-Memory Client Proxy
 *
 * stdio (MCP client) ↔ Unix socket (daemon) を透過的にブリッジする。
 * デーモンが未起動の場合は自動起動する。
 *
 * サブコマンド:
 *   sync  - Git-based CRDT同期操作
 *
 * @see kiri/src/client/proxy.ts
 */

import * as net from 'net';
import * as os from 'os';
import * as path from 'path';
import * as readline from 'readline';
import { parseArgs } from 'util';

import { getSocketPath } from '../shared/socket.js';
import { startDaemon, isDaemonRunning, stopDaemon } from './start-daemon.js';
import { DEFAULT_IDLE_TIMEOUT_MINUTES } from '../daemon/constants.js';
import { runSyncCommand } from '../cli/sync.js';

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

const SERVER_NAME = 'pce-memory';
const SERVER_VERSION = '0.1.0';

/**
 * CLI引数をパース
 */
function parseCliArgs() {
  const { values } = parseArgs({
    options: {
      db: { type: 'string', short: 'd' },
      'socket-path': { type: 'string', short: 's' },
      'daemon-timeout': { type: 'string', short: 't' },
      'no-daemon': { type: 'boolean' },
      help: { type: 'boolean', short: 'h' },
    },
    strict: true,
  });

  if (values.help) {
    console.error(`
${SERVER_NAME} v${SERVER_VERSION}

Usage: pce-memory [options]
       pce-memory sync <command> [options]

Subcommands:
  sync push      Export local DB to .pce-shared/
  sync pull      Import from .pce-shared/ to local DB
  sync status    Show sync directory status

  Run 'pce-memory sync --help' for sync subcommand details.

Options:
  -d, --db <path>            DuckDB file path (default: :memory:)
  -s, --socket-path <path>   Unix socket path (default: <db>.sock)
  -t, --daemon-timeout <min> Idle timeout in minutes (default: ${DEFAULT_IDLE_TIMEOUT_MINUTES})
  --no-daemon                Run in stdio mode without daemon
  -h, --help                 Show help
`);
    process.exit(0);
  }

  const databasePath = values.db || process.env['PCE_DB'] || ':memory:';
  const expandedDbPath = expandTilde(databasePath);
  const resolvedDbPath =
    expandedDbPath === ':memory:' ? expandedDbPath : path.resolve(expandedDbPath);
  const socketPath = values['socket-path']
    ? path.resolve(expandTilde(values['socket-path']))
    : resolvedDbPath === ':memory:'
      ? undefined
      : getSocketPath(resolvedDbPath);

  const idleTimeoutMinutes = values['daemon-timeout']
    ? parseInt(values['daemon-timeout'], 10)
    : DEFAULT_IDLE_TIMEOUT_MINUTES;

  return {
    databasePath: resolvedDbPath,
    socketPath,
    idleTimeoutMinutes: isNaN(idleTimeoutMinutes)
      ? DEFAULT_IDLE_TIMEOUT_MINUTES
      : idleTimeoutMinutes,
    noDaemon: values['no-daemon'] || resolvedDbPath === ':memory:',
  };
}

/**
 * デーモンのバージョンをチェック
 *
 * readlineを使用してバッファリングを適切に処理し、
 * 分割パケット受信に対応する。
 */
async function checkDaemonVersion(socket: net.Socket): Promise<void> {
  return new Promise((resolve, reject) => {
    const timeout = setTimeout(() => {
      rl.close();
      reject(new Error('Version check timeout'));
    }, 3000);

    const pingRequest = {
      jsonrpc: '2.0',
      id: 'version-check',
      method: 'ping',
    };

    // readlineでバッファリング処理（分割パケット対応）
    const rl = readline.createInterface({
      input: socket,
      crlfDelay: Infinity,
    });

    let responseReceived = false;

    rl.on('line', (line) => {
      if (responseReceived) return;

      try {
        const response = JSON.parse(line);
        if (response.id === 'version-check' && response.result) {
          responseReceived = true;
          clearTimeout(timeout);
          rl.close();

          const daemonVersion = response.result.serverInfo?.version || 'unknown';
          const clientVersion = SERVER_VERSION;

          const daemonMajorMinor = daemonVersion.split('.').slice(0, 2).join('.');
          const clientMajorMinor = clientVersion.split('.').slice(0, 2).join('.');

          if (daemonMajorMinor !== clientMajorMinor) {
            reject(
              new Error(
                `Version mismatch: client ${clientVersion} is incompatible with daemon ${daemonVersion}. Restart the daemon.`
              )
            );
          } else {
            console.error(
              `[Proxy] Version check passed: client=${clientVersion}, daemon=${daemonVersion}`
            );
            resolve();
          }
        }
      } catch {
        // JSON解析エラーは無視（他のメッセージの可能性）
        // タイムアウトまで待機
      }
    });

    rl.on('error', (err) => {
      clearTimeout(timeout);
      rl.close();
      reject(err);
    });

    socket.write(JSON.stringify(pingRequest) + '\n');
  });
}

/**
 * デーモンに接続を試みる（リトライロジック付き）
 */
async function connectToDaemon(
  socketPath: string,
  maxRetries: number,
  retryDelayMs: number
): Promise<net.Socket> {
  for (let attempt = 1; attempt <= maxRetries; attempt++) {
    try {
      const socket = net.connect(socketPath);

      await new Promise<void>((resolve, reject) => {
        socket.on('connect', () => resolve());
        socket.on('error', (err) => reject(err));
      });

      return socket;
    } catch (err) {
      console.error(
        `[Proxy] Connection attempt ${attempt}/${maxRetries} failed: ${(err as Error).message}`
      );

      if (attempt < maxRetries) {
        await new Promise((resolve) => setTimeout(resolve, retryDelayMs));
      } else {
        throw new Error(`Failed to connect to daemon after ${maxRetries} attempts.`);
      }
    }
  }

  throw new Error('Unexpected error in connectToDaemon');
}

/**
 * Stdio ↔ Socket ブリッジを確立
 */
function bridgeStdioToSocket(socket: net.Socket): void {
  // stdin → socket
  const stdinReader = readline.createInterface({
    input: process.stdin,
    crlfDelay: Infinity,
  });

  stdinReader.on('line', (line) => {
    socket.write(line + '\n');
  });

  stdinReader.on('close', () => {
    socket.end();
  });

  // socket → stdout
  const socketReader = readline.createInterface({
    input: socket,
    crlfDelay: Infinity,
  });

  socketReader.on('line', (line) => {
    console.log(line);
  });

  socket.on('end', () => {
    stdinReader.close();
    process.exit(0);
  });

  socket.on('error', (err) => {
    console.error(`[Proxy] Socket error: ${err.message}`);
    process.exit(1);
  });
}

/**
 * サブコマンドを検出してルーティング
 * サブコマンドが検出された場合は true を返し、処理を終了すべきことを示す
 */
async function handleSubcommand(): Promise<boolean> {
  const args = process.argv.slice(2);
  const [subcommand, ...subArgs] = args;

  if (subcommand === 'sync') {
    const exitCode = await runSyncCommand(subArgs);
    process.exit(exitCode);
  }

  return false;
}

/**
 * メイン関数：プロキシを起動
 */
async function main() {
  // サブコマンドをチェック（sync など）
  await handleSubcommand();

  const options = parseCliArgs();

  // --no-daemon または :memory: の場合は従来のstdioモードで起動
  if (options.noDaemon) {
    console.error('[Proxy] Running in stdio mode (no daemon)');
    // 動的インポートで従来のindex.tsを起動
    const indexModule = await import('../index.js');
    if (typeof indexModule.main === 'function') {
      await indexModule.main();
    }
    return;
  }

  if (!options.socketPath) {
    console.error('[Proxy] Error: socket path is required for daemon mode');
    process.exit(1);
  }

  try {
    // デーモンが実行中かチェック
    const running = await isDaemonRunning(options.databasePath);

    if (!running) {
      console.error('[Proxy] Daemon not running. Starting daemon...');

      await startDaemon({
        databasePath: options.databasePath,
        socketPath: options.socketPath,
        idleTimeoutMinutes: options.idleTimeoutMinutes,
      });

      console.error('[Proxy] Daemon started successfully');
    }

    // デーモンに接続
    const socket = await connectToDaemon(options.socketPath, 3, 1000);

    // バージョン互換性をチェック
    try {
      await checkDaemonVersion(socket);
    } catch (versionError) {
      const versionErr = versionError as Error;
      if (versionErr.message.includes('Version mismatch')) {
        console.error(`[Proxy] ${versionErr.message}`);
        console.error('[Proxy] Automatically restarting daemon...');

        socket.destroy();
        await stopDaemon(options.databasePath);
        await new Promise((resolve) => setTimeout(resolve, 1000));

        await startDaemon({
          databasePath: options.databasePath,
          socketPath: options.socketPath,
          idleTimeoutMinutes: options.idleTimeoutMinutes,
        });

        console.error('[Proxy] Daemon restarted, reconnecting...');

        const newSocket = await connectToDaemon(options.socketPath, 3, 1000);
        await checkDaemonVersion(newSocket);

        console.error('[Proxy] Connected to daemon. Bridging stdio ↔ socket...');
        bridgeStdioToSocket(newSocket);
        return;
      }
      throw versionError;
    }

    console.error('[Proxy] Connected to daemon. Bridging stdio ↔ socket...');
    bridgeStdioToSocket(socket);
  } catch (err) {
    const error = err as Error;
    console.error(`[Proxy] Failed to start proxy: ${error.message}`);
    console.error(`[Proxy] Check daemon log at: ${options.databasePath}.daemon.log`);
    process.exit(1);
  }
}

// エントリーポイント
main().catch((err) => {
  console.error(`[Proxy] Unhandled error: ${err}`);
  process.exit(1);
});

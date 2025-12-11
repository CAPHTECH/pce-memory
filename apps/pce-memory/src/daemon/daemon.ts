#!/usr/bin/env node
/**
 * PCE-Memory Daemon Main Process
 *
 * 単一デーモンプロセスとして複数クライアント接続を処理。
 * DuckDB接続を保持し、Unix socket経由でリクエストを受け付ける。
 */

import * as path from 'path';
import * as fs from 'fs/promises';
import { parseArgs } from 'util';

import { initDb, initSchema, closeDb } from '../db/connection.js';
import {
  initLocalProvider,
  disposeLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';
import { setEmbeddingService } from '../store/hybridSearch.js';
import { initRateState } from '../store/rate.js';
import { initMemoryState } from '../state/memoryState.js';
import { registerSystemLayer, getLayerScopeSummary } from '../state/layerScopeState.js';
import * as E from 'fp-ts/Either';

import { DaemonLifecycle } from './lifecycle.js';
import { createSocketServer } from './socket.js';
import { DAEMON_SHUTDOWN_WATCHDOG_MS, DEFAULT_IDLE_TIMEOUT_MINUTES } from './constants.js';
import type { JsonRpcRequest, JsonRpcResponse } from './socket.js';
import { getSocketPath } from '../shared/socket.js';
import { dispatchTool, TOOL_DEFINITIONS } from '../core/handlers.js';

const SERVER_NAME = 'pce-memory-daemon';
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
      help: { type: 'boolean', short: 'h' },
    },
    strict: true,
  });

  if (values.help) {
    console.log(`
${SERVER_NAME} v${SERVER_VERSION}

Usage: pce-daemon [options]

Options:
  -d, --db <path>            DuckDB file path (required)
  -s, --socket-path <path>   Unix socket path (default: <db>.sock)
  -t, --daemon-timeout <min> Idle timeout in minutes (default: ${DEFAULT_IDLE_TIMEOUT_MINUTES}, 0=disabled)
  -h, --help                 Show help
`);
    process.exit(0);
  }

  const databasePath = values.db;
  if (!databasePath) {
    console.error('Error: --db is required');
    process.exit(1);
  }

  const resolvedDbPath = path.resolve(databasePath);
  const socketPath = values['socket-path']
    ? path.resolve(values['socket-path'])
    : getSocketPath(resolvedDbPath, { ensureDir: true });

  const idleTimeoutMinutes = values['daemon-timeout'] ? parseInt(values['daemon-timeout'], 10) : DEFAULT_IDLE_TIMEOUT_MINUTES;

  return {
    databasePath: resolvedDbPath,
    socketPath,
    idleTimeoutMinutes: isNaN(idleTimeoutMinutes) ? DEFAULT_IDLE_TIMEOUT_MINUTES : idleTimeoutMinutes,
  };
}

/**
 * JSON-RPCリクエストハンドラ
 */
async function handleJsonRpcRequest(request: JsonRpcRequest): Promise<JsonRpcResponse | null> {
  const { method, params, id } = request;

  // pingリクエスト（ヘルスチェック用）
  if (method === 'ping') {
    return {
      jsonrpc: '2.0',
      id: id ?? null,
      result: {
        status: 'ok',
        serverInfo: {
          name: SERVER_NAME,
          version: SERVER_VERSION,
        },
      },
    };
  }

  // MCP initialize（MCPプロトコル必須）
  if (method === 'initialize') {
    return {
      jsonrpc: '2.0',
      id: id ?? null,
      result: {
        protocolVersion: '2024-11-05',
        capabilities: {
          tools: {},
        },
        serverInfo: {
          name: SERVER_NAME,
          version: SERVER_VERSION,
        },
      },
    };
  }

  // MCP notifications/initialized（初期化完了通知、レスポンス不要）
  if (method === 'notifications/initialized') {
    // 通知なのでレスポンスは不要
    return null;
  }

  // MCP tools/list（ツール一覧）
  if (method === 'tools/list') {
    return {
      jsonrpc: '2.0',
      id: id ?? null,
      result: { tools: TOOL_DEFINITIONS },
    };
  }

  // MCP tools/call（ツール呼び出し）
  if (method === 'tools/call') {
    const toolName = (params as Record<string, unknown>)?.['name'] as string;
    const toolArgs = ((params as Record<string, unknown>)?.['arguments'] ?? {}) as Record<
      string,
      unknown
    >;

    const result = await dispatchTool(toolName, toolArgs);

    return {
      jsonrpc: '2.0',
      id: id ?? null,
      result,
    };
  }

  // 未知のメソッド
  return {
    jsonrpc: '2.0',
    id: id ?? null,
    error: {
      code: -32601,
      message: `Method not found: ${method}`,
    },
  };
}

/**
 * メイン関数
 */
async function main() {
  const options = parseCliArgs();
  const lifecycle = new DaemonLifecycle(options.databasePath, options.idleTimeoutMinutes);

  try {
    // スタートアップロックを取得
    const lockAcquired = await lifecycle.acquireStartupLock();
    if (!lockAcquired) {
      console.error('[Daemon] Another daemon is starting up. Exiting.');
      process.exit(1);
    }

    await lifecycle.log(`Starting daemon for database: ${options.databasePath}`);

    // PIDファイルを作成
    await lifecycle.createPidFile();
    console.error(`[Daemon] PID: ${process.pid}`);

    // DBディレクトリを作成
    const dbDir = path.dirname(options.databasePath);
    await fs.mkdir(dbDir, { recursive: true });

    // 環境変数を設定してDB初期化
    process.env['PCE_DB'] = options.databasePath;
    await initDb();
    await initSchema();
    await initRateState();

    // EmbeddingService初期化
    try {
      await initLocalProvider();
      const embeddingCache = createInMemoryCache({
        initialModelVersion: localProvider.modelVersion,
      });
      const embeddingService = createLocalOnlyService(localProvider, embeddingCache);
      setEmbeddingService(embeddingService);
      console.error(`[Daemon] EmbeddingService initialized (model: ${localProvider.modelVersion})`);
    } catch (e: unknown) {
      console.error(
        `[Daemon] EmbeddingService initialization failed (fallback to text-only search):`,
        e
      );
    }

    // システムLayer登録
    const dbLayerResult = registerSystemLayer('db', new Set(['db_access'] as const), new Set());
    if (E.isLeft(dbLayerResult)) {
      console.error(`[Daemon] Failed to register db layer: ${dbLayerResult.left.message}`);
    }

    const policyLayerResult = registerSystemLayer(
      'policy',
      new Set(['policy_check'] as const),
      new Set(['db'])
    );
    if (E.isLeft(policyLayerResult)) {
      console.error(`[Daemon] Failed to register policy layer: ${policyLayerResult.left.message}`);
    }

    const schemaLayerResult = registerSystemLayer(
      'schema',
      new Set(['schema_validate'] as const),
      new Set(['db'])
    );
    if (E.isLeft(schemaLayerResult)) {
      console.error(`[Daemon] Failed to register schema layer: ${schemaLayerResult.left.message}`);
    }

    console.error(`[Daemon] System layers registered: ${getLayerScopeSummary().layers.join(', ')}`);

    // 状態復元
    const initResult = await initMemoryState()();
    if (E.isLeft(initResult)) {
      console.error(`[Daemon] Failed to initialize state: ${initResult.left.message}`);
    } else {
      console.error(
        `[Daemon] Restored state: ${initResult.right.state} (policy: ${initResult.right.policyVersion})`
      );
    }

    // ソケットサーバーを作成
    // 接続ベースのアイドル判定: ソケット接続が維持されている間はシャットダウンしない
    const closeServer = await createSocketServer({
      socketPath: options.socketPath,
      onRequest: async (request) => {
        return await handleJsonRpcRequest(request);
      },
      onError: async (error) => {
        await lifecycle.log(`Connection error: ${error.message}`);
        console.error(`[Daemon] Connection error: ${error.message}`);
      },
      // 接続確立時にカウントアップ（アイドルタイマーリセット）
      onConnect: () => {
        lifecycle.incrementConnections();
      },
      // 接続終了時にカウントダウン（全接続終了後にアイドルタイマー開始）
      onDisconnect: () => {
        lifecycle.decrementConnections();
      },
    });

    await lifecycle.log(`Socket server listening on: ${options.socketPath}`);

    // スタートアップロックを解放（起動完了）
    await lifecycle.releaseStartupLock();

    // グレースフルシャットダウンの設定（ウォッチドッグタイマー付き）
    // タイムアウト値は constants.ts で一元管理

    lifecycle.onShutdown(async () => {
      // ウォッチドッグ: 全体のシャットダウンが指定時間内に完了しない場合は強制終了
      const watchdog = setTimeout(() => {
        console.error('[Daemon] Shutdown watchdog triggered. Force exiting.');
        process.exit(1);
      }, DAEMON_SHUTDOWN_WATCHDOG_MS);
      watchdog.unref(); // プロセス終了をブロックしない

      try {
        await lifecycle.log('Shutting down daemon...');
        console.error('[Daemon] Closing server...');
        await closeServer();

        // ONNX Runtimeを先に破棄（mutex例外防止）
        console.error('[Daemon] Disposing embedding provider...');
        await disposeLocalProvider();

        console.error('[Daemon] Closing database...');
        await closeDb();

        console.error('[Daemon] Shutdown complete.');
      } finally {
        clearTimeout(watchdog);
      }
    });

    lifecycle.setupGracefulShutdown();

    await lifecycle.log('Daemon started successfully');
    console.error('[Daemon] Ready to accept connections');
  } catch (err) {
    const error = err as Error;
    await lifecycle.log(`Fatal error: ${error.message}`);
    console.error(`[Daemon] Fatal error: ${error.message}`);
    await lifecycle.removePidFile();
    await lifecycle.releaseStartupLock();
    process.exit(1);
  }
}

// エントリーポイント
main().catch(async (err) => {
  console.error(`[Daemon] Unhandled error: ${err}`);
  process.exit(1);
});

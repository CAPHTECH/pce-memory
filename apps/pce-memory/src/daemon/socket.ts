/**
 * IPC Transport Layer for PCE-Memory Daemon
 *
 * Unix domain sockets（macOS/Linux）/ Named pipes（Windows）を使用した
 * 複数クライアント同時接続対応のJSON-RPCサーバー。
 *
 * @see kiri/src/daemon/socket.ts
 */

import * as fs from "fs/promises";
import * as net from "net";
import * as os from "os";
import * as readline from "readline";

import { acquireLock, releaseLock } from "../shared/lockfile.js";

/**
 * JSON-RPCリクエスト型
 */
export interface JsonRpcRequest {
  jsonrpc: "2.0";
  id?: string | number | null;
  method: string;
  params?: Record<string, unknown>;
}

/**
 * JSON-RPCレスポンス型
 */
export interface JsonRpcResponse {
  jsonrpc: "2.0";
  id: string | number | null;
  result?: unknown;
  error?: {
    code: number;
    message: string;
    data?: unknown;
  };
}

/**
 * ソケットサーバー設定
 */
export interface SocketServerOptions {
  /** ソケットパス（Unix socket file path または Windows named pipe） */
  socketPath: string;
  /** JSON-RPCリクエストハンドラ */
  onRequest: (request: JsonRpcRequest) => Promise<JsonRpcResponse | null>;
  /** エラーハンドラ（オプション） */
  onError?: (error: Error) => void;
}

/**
 * ソケットサーバーを作成し、複数クライアント接続を処理する
 *
 * @param options - サーバー設定
 * @returns クリーンアップ用のcloseハンドラ
 */
export async function createSocketServer(
  options: SocketServerOptions
): Promise<() => Promise<void>> {
  const { socketPath, onRequest, onError } = options;
  const isWindows = os.platform() === "win32";

  // 排他ロックでデーモン重複起動を防止
  const lockfilePath = `${socketPath}.lock`;
  try {
    acquireLock(lockfilePath);
  } catch (error) {
    const err = error as Error;
    throw new Error(
      `Failed to acquire daemon lock: ${err.message}. ` +
        `Another daemon may be running. Lock file: ${lockfilePath}`
    );
  }

  // Unix系: 既存ソケットファイルを削除
  if (!isWindows) {
    try {
      await fs.unlink(socketPath);
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== "ENOENT") {
        throw err;
      }
    }
  }

  const server = net.createServer((socket) => {
    handleClientConnection(socket, onRequest, onError);
  });

  // ソケット/名前付きパイプをリッスン
  await new Promise<void>((resolve, reject) => {
    server.listen(socketPath, () => {
      resolve();
    });

    server.on("error", (err: NodeJS.ErrnoException) => {
      if (err.code === "EADDRINUSE") {
        const msg = isWindows
          ? `Named pipe already in use: ${socketPath}. Another daemon may be running.`
          : `Socket file in use: ${socketPath}. Another daemon may be running.`;
        reject(new Error(msg));
      } else if (err.code === "EACCES") {
        reject(
          new Error(
            `Permission denied for socket: ${socketPath}. Check permissions.`
          )
        );
      } else {
        reject(new Error(`Failed to listen on ${socketPath}: ${err.message}`));
      }
    });
  });

  // Unix系: ソケットファイルのパーミッションを0600に設定
  if (!isWindows) {
    await fs.chmod(socketPath, 0o600);
  }

  console.error(`[Daemon] Listening on socket: ${socketPath}`);

  // クリーンアップハンドラを返す
  return async () => {
    return new Promise<void>((resolve) => {
      server.close(async () => {
        releaseLock(lockfilePath);

        if (!isWindows) {
          try {
            await fs.unlink(socketPath);
          } catch {
            // 削除エラーは無視
          }
        }
        resolve();
      });
    });
  };
}

/**
 * クライアント接続を処理
 */
function handleClientConnection(
  socket: net.Socket,
  onRequest: (request: JsonRpcRequest) => Promise<JsonRpcResponse | null>,
  onError?: (error: Error) => void
): void {
  const rl = readline.createInterface({
    input: socket,
    crlfDelay: Infinity,
  });

  rl.on("line", async (line) => {
    let request: JsonRpcRequest | null = null;
    try {
      request = JSON.parse(line) as JsonRpcRequest;
    } catch (err) {
      const error = err as Error;
      if (onError) {
        onError(error);
      }

      const errorResponse: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: null,
        error: {
          code: -32700,
          message: "Parse error: Invalid JSON received.",
        },
      };
      socket.write(JSON.stringify(errorResponse) + "\n");
      return;
    }

    try {
      const result = await onRequest(request);
      if (result) {
        const hasResponseId = typeof request.id === "string" || typeof request.id === "number";
        if (!hasResponseId) {
          return; // notification（idなし）にはレスポンス不要
        }
        socket.write(JSON.stringify(result) + "\n");
      }
    } catch (err) {
      const error = err as Error;
      if (onError) {
        onError(error);
      }

      const hasResponseId =
        request && (typeof request.id === "string" || typeof request.id === "number");
      if (!hasResponseId) {
        return;
      }

      const errorResponse: JsonRpcResponse = {
        jsonrpc: "2.0",
        id: request.id ?? null,
        error: {
          code: -32603,
          message: `Internal error: ${error.message}`,
        },
      };
      socket.write(JSON.stringify(errorResponse) + "\n");
    }
  });

  socket.on("error", (err) => {
    if (onError) {
      onError(err);
    }
  });

  socket.on("end", () => {
    rl.close();
  });
}

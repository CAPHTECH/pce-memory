/**
 * Socket Path Utility for Cross-Platform IPC
 *
 * プラットフォームに応じた適切なIPCパスを生成:
 * - Unix/Linux/macOS: Unix domain socket files (e.g., /path/to/database.duckdb.sock)
 * - Windows: Named pipes (e.g., \\.\pipe\pce-<hash>)
 *
 * @see kiri/src/shared/utils/socket.ts
 */

import * as crypto from "crypto";
import { mkdirSync } from "node:fs";
import * as os from "os";
import * as path from "path";

/** macOS 104-byte制限に安全マージンを残す */
const UNIX_SOCKET_PATH_MAX = 96;

/** ソケット/パイプ名のプレフィックス */
const SOCKET_PREFIX = "pce";

/** ソケットディレクトリの環境変数名 */
const SOCKET_DIR_ENV = "PCE_SOCKET_DIR";

/**
 * ファイル名をサニタイズ
 */
function sanitizeBaseName(fileName: string): string {
  const sanitized = fileName.replace(/[^a-zA-Z0-9]/g, "-");
  return sanitized.length > 0 ? sanitized.toLowerCase() : "db";
}

/**
 * ソケットディレクトリを作成
 */
function ensureSocketDir(dirPath: string): void {
  try {
    mkdirSync(dirPath, { recursive: true, mode: 0o700 });
  } catch (error) {
    const err = error as NodeJS.ErrnoException;
    throw new Error(
      `Failed to prepare socket directory ${dirPath}: ${err.message}. ` +
        `Set ${SOCKET_DIR_ENV} to a writable directory.`
    );
  }
}

/**
 * パス長制限を超える場合のフォールバックパスを構築
 */
function buildFallbackUnixSocketPath(databasePath: string, ensureDir: boolean): string {
  const fallbackDir = process.env[SOCKET_DIR_ENV] || os.tmpdir();
  const hash = crypto.createHash("sha256").update(databasePath).digest("hex");
  const baseName = sanitizeBaseName(path.basename(databasePath));

  const candidates = [
    path.join(fallbackDir, `${SOCKET_PREFIX}-${baseName}-${hash.slice(0, 12)}.sock`),
    path.join(fallbackDir, `${SOCKET_PREFIX}-${hash.slice(0, 12)}.sock`),
    path.join(fallbackDir, `${SOCKET_PREFIX}-${hash.slice(0, 8)}.sock`),
  ];

  for (const candidate of candidates) {
    if (Buffer.byteLength(candidate, "utf8") <= UNIX_SOCKET_PATH_MAX) {
      if (ensureDir) {
        ensureSocketDir(path.dirname(candidate));
      }
      return candidate;
    }
  }

  throw new Error(
    `Unable to construct Unix socket path under ${UNIX_SOCKET_PATH_MAX} characters. ` +
      `Set ${SOCKET_DIR_ENV} to a shorter directory.`
  );
}

/**
 * プラットフォームに応じた適切なソケットパスを生成
 *
 * Windows環境では名前付きパイプ形式（\\.\pipe\pce-<hash>）を使用し、
 * Unix系環境ではファイルシステムパス（<databasePath>.sock）を使用し、
 * パス長が上限を超える場合は /tmp などの短いディレクトリに自動フォールバックする。
 *
 * セキュリティ:
 * - Unix: ソケットファイルは0600パーミッション（所有者のみアクセス可能）で保護
 * - Windows: 名前付きパイプはデフォルトACLを使用
 *
 * @param databasePath - データベースファイルの絶対パス
 * @param options - オプション（ensureDir: ディレクトリを作成するか）
 * @returns プラットフォーム固有のソケットパス
 */
export function getSocketPath(databasePath: string, options?: { ensureDir?: boolean }): string {
  const ensureDir = options?.ensureDir ?? false;

  if (os.platform() === "win32") {
    // Windows: 名前付きパイプを使用
    const hash = crypto.createHash("sha256").update(databasePath).digest("hex");
    const prefix = process.env["PCE_PIPE_PREFIX"] || SOCKET_PREFIX;
    const pipeName = `${prefix}-${hash.substring(0, 16)}`;
    return `\\\\.\\pipe\\${pipeName}`;
  }

  // Unix系: データベースパスに.sockを追加
  const defaultSocketPath = `${databasePath}.sock`;
  if (Buffer.byteLength(defaultSocketPath, "utf8") <= UNIX_SOCKET_PATH_MAX) {
    if (ensureDir) {
      ensureSocketDir(path.dirname(defaultSocketPath));
    }
    return defaultSocketPath;
  }

  // パスが長すぎる場合はフォールバック
  return buildFallbackUnixSocketPath(databasePath, ensureDir);
}

/**
 * ソケットパスからデータベースパスを推測（Unix系のみ）
 *
 * @param socketPath - ソケットパス
 * @returns データベースパス（Unix系の場合）またはnull（Windows/不明な形式）
 */
export function getDatabasePathFromSocket(socketPath: string): string | null {
  if (os.platform() === "win32") {
    return null;
  }

  if (socketPath.endsWith(".sock")) {
    return socketPath.slice(0, -5);
  }

  return null;
}

/**
 * デバッグ用のソケットパス情報を生成
 */
export function getSocketPathDebugInfo(databasePath: string): string {
  const socketPath = getSocketPath(databasePath);
  const platform = os.platform();
  const defaultUnixSocket = `${databasePath}.sock`;

  const pathModule = platform === "win32" ? path.win32 : path.posix;
  const dbDir = pathModule.dirname(databasePath);
  const dbBase = pathModule.basename(databasePath);

  if (platform === "win32") {
    return [
      `Database: ${dbBase} (${dbDir})`,
      `Socket: ${socketPath} (Windows named pipe)`,
      `Note: Pipe name is derived from database path hash for uniqueness`,
    ].join("\n");
  } else {
    const lines = [
      `Database: ${dbBase} (${dbDir})`,
      `Socket: ${socketPath} (Unix domain socket)`,
      `Permissions: Owner-only (0600)`,
    ];

    if (socketPath !== defaultUnixSocket) {
      lines.push(
        `Fallback: Socket path shortened (set ${SOCKET_DIR_ENV} to override base directory)`
      );
    }

    return lines.join("\n");
  }
}

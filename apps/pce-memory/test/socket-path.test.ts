/**
 * Socket Path Module Unit Tests
 *
 * ソケットパス生成のテスト:
 * - Unix socket path生成
 * - パス長制限のフォールバック
 *
 * Note: ESMではos.platformをモックできないため、
 * 現在のプラットフォームでのテストのみ実行
 */

import { describe, it, expect } from 'vitest';
import * as os from 'os';
import * as path from 'path';

import {
  getSocketPath,
  getDatabasePathFromSocket,
  getSocketPathDebugInfo,
} from '../src/shared/socket.js';

const isWindows = os.platform() === 'win32';

describe('socket path utilities', () => {
  describe('getSocketPath', () => {
    if (!isWindows) {
      describe('on Unix-like systems', () => {
        it('should append .sock to database path', () => {
          const dbPath = '/tmp/test.db';
          const socketPath = getSocketPath(dbPath);
          expect(socketPath).toBe('/tmp/test.db.sock');
        });

        it('should handle path with spaces', () => {
          const dbPath = '/tmp/my database.db';
          const socketPath = getSocketPath(dbPath);
          expect(socketPath).toBe('/tmp/my database.db.sock');
        });

        it('should use fallback for very long paths', () => {
          // 96バイトを超える長いパス
          const longDir =
            '/very/long/path/that/exceeds/the/unix/socket/path/limit/of/about/one/hundred/four/bytes';
          const dbPath = path.join(longDir, 'database.db');
          const socketPath = getSocketPath(dbPath);

          // フォールバックが使用され、パスが短くなっている
          expect(Buffer.byteLength(socketPath, 'utf8')).toBeLessThanOrEqual(96);
          expect(socketPath).toMatch(/\.sock$/);
        });

        it('should handle relative paths', () => {
          const dbPath = './test.db';
          const socketPath = getSocketPath(dbPath);
          expect(socketPath).toBe('./test.db.sock');
        });

        it('should handle paths with special characters', () => {
          const dbPath = '/tmp/test-db_v1.2.3.db';
          const socketPath = getSocketPath(dbPath);
          expect(socketPath).toBe('/tmp/test-db_v1.2.3.db.sock');
        });
      });
    } else {
      describe('on Windows', () => {
        it('should return named pipe path', () => {
          const dbPath = 'C:\\Users\\test\\database.db';
          const socketPath = getSocketPath(dbPath);

          expect(socketPath).toMatch(/^\\\\\.\\pipe\\pce-[a-f0-9]+$/);
        });

        it('should generate unique paths for different databases', () => {
          const dbPath1 = 'C:\\db1.db';
          const dbPath2 = 'C:\\db2.db';

          const socketPath1 = getSocketPath(dbPath1);
          const socketPath2 = getSocketPath(dbPath2);

          expect(socketPath1).not.toBe(socketPath2);
        });
      });
    }

    it('should generate consistent path for same database', () => {
      const dbPath = isWindows ? 'C:\\test.db' : '/tmp/test.db';
      const socketPath1 = getSocketPath(dbPath);
      const socketPath2 = getSocketPath(dbPath);

      expect(socketPath1).toBe(socketPath2);
    });

    it('should generate different paths for different databases', () => {
      const dbPath1 = isWindows ? 'C:\\db1.db' : '/tmp/db1.db';
      const dbPath2 = isWindows ? 'C:\\db2.db' : '/tmp/db2.db';

      const socketPath1 = getSocketPath(dbPath1);
      const socketPath2 = getSocketPath(dbPath2);

      expect(socketPath1).not.toBe(socketPath2);
    });
  });

  describe('getDatabasePathFromSocket', () => {
    if (!isWindows) {
      it('should extract database path from socket path', () => {
        const socketPath = '/tmp/test.db.sock';
        const dbPath = getDatabasePathFromSocket(socketPath);
        expect(dbPath).toBe('/tmp/test.db');
      });

      it('should return null for non-.sock paths', () => {
        const socketPath = '/tmp/test.socket';
        const dbPath = getDatabasePathFromSocket(socketPath);
        expect(dbPath).toBeNull();
      });

      it('should handle paths with multiple dots', () => {
        const socketPath = '/tmp/test.v1.2.db.sock';
        const dbPath = getDatabasePathFromSocket(socketPath);
        expect(dbPath).toBe('/tmp/test.v1.2.db');
      });
    } else {
      it('should return null on Windows', () => {
        const socketPath = '\\\\.\\pipe\\pce-abc123';
        const dbPath = getDatabasePathFromSocket(socketPath);
        expect(dbPath).toBeNull();
      });
    }
  });

  describe('getSocketPathDebugInfo', () => {
    it('should return debug info string', () => {
      const dbPath = isWindows ? 'C:\\test.db' : '/tmp/test.db';
      const info = getSocketPathDebugInfo(dbPath);

      expect(typeof info).toBe('string');
      expect(info).toContain('Database:');
      expect(info).toContain('Socket:');
    });

    if (!isWindows) {
      it('should mention Unix domain socket', () => {
        const dbPath = '/tmp/test.db';
        const info = getSocketPathDebugInfo(dbPath);
        expect(info).toContain('Unix domain socket');
      });

      it('should mention permissions', () => {
        const dbPath = '/tmp/test.db';
        const info = getSocketPathDebugInfo(dbPath);
        expect(info).toContain('0600');
      });

      it('should indicate fallback when path is shortened', () => {
        const longPath =
          '/very/long/path/that/will/definitely/exceed/the/maximum/allowed/length/for/unix/sockets/database.db';
        const info = getSocketPathDebugInfo(longPath);
        expect(info).toContain('Fallback');
      });
    } else {
      it('should mention Windows named pipe', () => {
        const dbPath = 'C:\\test.db';
        const info = getSocketPathDebugInfo(dbPath);
        expect(info).toContain('Windows named pipe');
      });
    }
  });
});

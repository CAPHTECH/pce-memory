/**
 * Daemon Constants Module Unit Tests
 *
 * シャットダウン関連の定数のテスト:
 * - タイムアウト値の関係性検証
 * - 定数のエクスポート確認
 */

import { describe, it, expect } from 'vitest';

import {
  SOCKET_SHUTDOWN_TIMEOUT_MS,
  DAEMON_SHUTDOWN_WATCHDOG_MS,
} from '../src/daemon/constants.js';

describe('daemon constants', () => {
  describe('timeout values', () => {
    it('should have SOCKET_SHUTDOWN_TIMEOUT_MS less than DAEMON_SHUTDOWN_WATCHDOG_MS', () => {
      // ソケットタイムアウトはウォッチドッグより短くなければならない
      // （ソケットが先にタイムアウトし、その後ウォッチドッグが発動する設計）
      expect(SOCKET_SHUTDOWN_TIMEOUT_MS).toBeLessThan(DAEMON_SHUTDOWN_WATCHDOG_MS);
    });

    it('should have reasonable timeout values', () => {
      // 最小値: 1秒以上（短すぎるとシャットダウンが間に合わない）
      expect(SOCKET_SHUTDOWN_TIMEOUT_MS).toBeGreaterThanOrEqual(1000);
      expect(DAEMON_SHUTDOWN_WATCHDOG_MS).toBeGreaterThanOrEqual(1000);

      // 最大値: 60秒以下（長すぎるとユーザー体験が悪い）
      expect(SOCKET_SHUTDOWN_TIMEOUT_MS).toBeLessThanOrEqual(60000);
      expect(DAEMON_SHUTDOWN_WATCHDOG_MS).toBeLessThanOrEqual(60000);
    });

    it('should have enough buffer between timeouts', () => {
      // ウォッチドッグはソケットタイムアウトの少なくとも1.5倍以上
      // （処理のオーバーヘッドを考慮）
      const minimumBuffer = SOCKET_SHUTDOWN_TIMEOUT_MS * 1.5;
      expect(DAEMON_SHUTDOWN_WATCHDOG_MS).toBeGreaterThanOrEqual(minimumBuffer);
    });
  });

  describe('exported values', () => {
    it('should export SOCKET_SHUTDOWN_TIMEOUT_MS as number', () => {
      expect(typeof SOCKET_SHUTDOWN_TIMEOUT_MS).toBe('number');
      expect(Number.isInteger(SOCKET_SHUTDOWN_TIMEOUT_MS)).toBe(true);
    });

    it('should export DAEMON_SHUTDOWN_WATCHDOG_MS as number', () => {
      expect(typeof DAEMON_SHUTDOWN_WATCHDOG_MS).toBe('number');
      expect(Number.isInteger(DAEMON_SHUTDOWN_WATCHDOG_MS)).toBe(true);
    });
  });
});

describe('socket module re-export', () => {
  it('should re-export SOCKET_SHUTDOWN_TIMEOUT_MS from socket module', async () => {
    // socket.ts からも同じ値がエクスポートされていることを確認
    const { SOCKET_SHUTDOWN_TIMEOUT_MS: fromSocket } = await import('../src/daemon/socket.js');
    expect(fromSocket).toBe(SOCKET_SHUTDOWN_TIMEOUT_MS);
  });
});

/**
 * Lockfile Module Unit Tests
 *
 * ロックファイル管理のテスト:
 * - 排他的ロック取得
 * - Stale lock検出・削除
 * - ロック解放（冪等性）
 */

import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';

import {
  acquireLock,
  releaseLock,
  isLocked,
  getLockOwner,
  LockfileError,
} from '../src/shared/lockfile.js';

describe('lockfile', () => {
  let testDir: string;
  let lockfilePath: string;

  beforeEach(() => {
    // テスト用一時ディレクトリを作成
    testDir = fs.mkdtempSync(path.join(os.tmpdir(), 'lockfile-test-'));
    lockfilePath = path.join(testDir, 'test.lock');
  });

  afterEach(() => {
    // テスト後のクリーンアップ
    try {
      if (fs.existsSync(lockfilePath)) {
        fs.unlinkSync(lockfilePath);
      }
      fs.rmdirSync(testDir);
    } catch {
      // クリーンアップエラーは無視
    }
  });

  describe('acquireLock', () => {
    it('should acquire lock successfully when no lock exists', () => {
      // ロックが存在しない状態で取得
      expect(() => acquireLock(lockfilePath)).not.toThrow();

      // ロックファイルが作成されている
      expect(fs.existsSync(lockfilePath)).toBe(true);

      // 現在のPIDが書き込まれている
      const content = fs.readFileSync(lockfilePath, 'utf8');
      expect(content).toBe(String(process.pid));
    });

    it('should throw LockfileError when lock is held by another process', () => {
      // 現在のプロセスでロックを取得
      acquireLock(lockfilePath);

      // 別のロックファイルパスで同じテスト
      const lockfilePath2 = path.join(testDir, 'test2.lock');

      // 現在のプロセスのPIDでロックファイルを作成（自分自身をシミュレート）
      fs.writeFileSync(lockfilePath2, String(process.pid), { flag: 'wx' });

      // 同じPIDでは取得できない（既にロック中）
      expect(() => acquireLock(lockfilePath2)).toThrow(LockfileError);

      try {
        acquireLock(lockfilePath2);
      } catch (e) {
        const error = e as LockfileError;
        expect(error.lockfilePath).toBe(lockfilePath2);
        expect(error.ownerPid).toBe(process.pid);
        expect(error.message).toContain('Another process');
      }

      // クリーンアップ
      fs.unlinkSync(lockfilePath2);
    });

    it('should detect and remove stale lock from dead process', () => {
      // 存在しないPID（非常に大きい数値）でロックファイルを作成
      const deadPid = 999999999;
      fs.writeFileSync(lockfilePath, String(deadPid), { flag: 'wx' });

      // ロック取得を試みる（stale lockとして削除されるべき）
      expect(() => acquireLock(lockfilePath)).not.toThrow();

      // 現在のPIDで上書きされている
      const content = fs.readFileSync(lockfilePath, 'utf8');
      expect(content).toBe(String(process.pid));
    });

    it('should handle invalid PID content gracefully', () => {
      // 不正な内容のロックファイル
      fs.writeFileSync(lockfilePath, 'not-a-number', { flag: 'wx' });

      // 安全のため、アクティブとみなしてエラーを投げる
      expect(() => acquireLock(lockfilePath)).toThrow(LockfileError);
    });

    it('should handle empty lock file', () => {
      // 空のロックファイル
      fs.writeFileSync(lockfilePath, '', { flag: 'wx' });

      // 安全のため、アクティブとみなしてエラーを投げる
      expect(() => acquireLock(lockfilePath)).toThrow(LockfileError);
    });
  });

  describe('releaseLock', () => {
    it('should release existing lock', () => {
      // ロックを取得
      acquireLock(lockfilePath);
      expect(fs.existsSync(lockfilePath)).toBe(true);

      // ロックを解放
      releaseLock(lockfilePath);
      expect(fs.existsSync(lockfilePath)).toBe(false);
    });

    it('should be idempotent (no error when lock does not exist)', () => {
      // 存在しないロックを解放してもエラーにならない
      expect(() => releaseLock(lockfilePath)).not.toThrow();
      expect(() => releaseLock(lockfilePath)).not.toThrow();
    });
  });

  describe('isLocked', () => {
    it('should return true when lock file exists', () => {
      fs.writeFileSync(lockfilePath, '123');
      expect(isLocked(lockfilePath)).toBe(true);
    });

    it('should return false when lock file does not exist', () => {
      expect(isLocked(lockfilePath)).toBe(false);
    });
  });

  describe('getLockOwner', () => {
    it('should return PID when lock file exists with valid content', () => {
      fs.writeFileSync(lockfilePath, '12345');
      expect(getLockOwner(lockfilePath)).toBe(12345);
    });

    it('should return null when lock file does not exist', () => {
      expect(getLockOwner(lockfilePath)).toBeNull();
    });

    it('should return null when lock file contains invalid content', () => {
      fs.writeFileSync(lockfilePath, 'not-a-number');
      expect(getLockOwner(lockfilePath)).toBeNull();
    });

    it('should return null for empty lock file', () => {
      fs.writeFileSync(lockfilePath, '');
      expect(getLockOwner(lockfilePath)).toBeNull();
    });
  });

  describe('LockfileError', () => {
    it('should have correct properties', () => {
      const error = new LockfileError('test message', '/path/to/lock', 123);

      expect(error.name).toBe('LockfileError');
      expect(error.message).toBe('test message');
      expect(error.lockfilePath).toBe('/path/to/lock');
      expect(error.ownerPid).toBe(123);
    });

    it('should work without ownerPid', () => {
      const error = new LockfileError('test message', '/path/to/lock');

      expect(error.ownerPid).toBeUndefined();
    });
  });
});

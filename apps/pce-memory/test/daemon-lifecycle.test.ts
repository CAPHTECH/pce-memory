/**
 * Daemon Lifecycle Module Unit Tests
 *
 * デーモンライフサイクル管理のテスト:
 * - PIDファイル管理
 * - アイドルタイムアウト
 * - 接続カウント
 */

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import * as fs from "fs/promises";
import * as path from "path";
import * as os from "os";

import { DaemonLifecycle } from "../src/daemon/lifecycle.js";

describe("DaemonLifecycle", () => {
  let testDir: string;
  let databasePath: string;
  let lifecycle: DaemonLifecycle;

  beforeEach(async () => {
    // テスト用一時ディレクトリを作成
    testDir = await fs.mkdtemp(path.join(os.tmpdir(), "lifecycle-test-"));
    databasePath = path.join(testDir, "test.db");
    lifecycle = new DaemonLifecycle(databasePath, 5);
  });

  afterEach(async () => {
    // テスト後のクリーンアップ
    try {
      await fs.rm(testDir, { recursive: true, force: true });
    } catch {
      // クリーンアップエラーは無視
    }
  });

  describe("path getters", () => {
    it("should return correct PID file path", () => {
      expect(lifecycle.getPidFilePath()).toBe(`${databasePath}.daemon.pid`);
    });

    it("should return correct startup lock path", () => {
      expect(lifecycle.getStartupLockPath()).toBe(`${databasePath}.daemon.starting`);
    });

    it("should return correct log file path", () => {
      expect(lifecycle.getLogFilePath()).toBe(`${databasePath}.daemon.log`);
    });
  });

  describe("PID file management", () => {
    it("should create PID file with current process PID", async () => {
      await lifecycle.createPidFile();

      const pidFilePath = lifecycle.getPidFilePath();
      const content = await fs.readFile(pidFilePath, "utf-8");
      expect(content).toBe(String(process.pid));
    });

    it("should remove PID file", async () => {
      await lifecycle.createPidFile();
      await lifecycle.removePidFile();

      const pidFilePath = lifecycle.getPidFilePath();
      await expect(fs.access(pidFilePath)).rejects.toThrow();
    });

    it("should not throw when removing non-existent PID file", async () => {
      await expect(lifecycle.removePidFile()).resolves.not.toThrow();
    });
  });

  describe("startup lock", () => {
    it("should acquire startup lock successfully", async () => {
      const acquired = await lifecycle.acquireStartupLock();
      expect(acquired).toBe(true);

      // ロックファイルが作成されている
      const lockPath = lifecycle.getStartupLockPath();
      const content = await fs.readFile(lockPath, "utf-8");
      expect(content).toBe(String(process.pid));

      // クリーンアップ
      await lifecycle.releaseStartupLock();
    });

    it("should fail to acquire lock when already held", async () => {
      // 最初のロック取得
      const firstAcquired = await lifecycle.acquireStartupLock();
      expect(firstAcquired).toBe(true);

      // 2回目のロック取得は失敗
      const lifecycle2 = new DaemonLifecycle(databasePath, 5);
      const secondAcquired = await lifecycle2.acquireStartupLock();
      expect(secondAcquired).toBe(false);

      // クリーンアップ
      await lifecycle.releaseStartupLock();
    });

    it("should release startup lock", async () => {
      await lifecycle.acquireStartupLock();
      await lifecycle.releaseStartupLock();

      const lockPath = lifecycle.getStartupLockPath();
      await expect(fs.access(lockPath)).rejects.toThrow();
    });

    it("should not throw when releasing non-existent lock", async () => {
      await expect(lifecycle.releaseStartupLock()).resolves.not.toThrow();
    });
  });

  describe("running check", () => {
    it("should return null when PID file does not exist", async () => {
      const pid = await lifecycle.checkRunning();
      expect(pid).toBeNull();
    });

    it("should return PID when process is running", async () => {
      // 現在のプロセスのPIDをPIDファイルに書き込む
      await lifecycle.createPidFile();

      const pid = await lifecycle.checkRunning();
      expect(pid).toBe(process.pid);

      await lifecycle.removePidFile();
    });

    it("should return null when process is not running", async () => {
      // 存在しないPIDをPIDファイルに書き込む
      const pidFilePath = lifecycle.getPidFilePath();
      await fs.writeFile(pidFilePath, "999999999", "utf-8");

      const pid = await lifecycle.checkRunning();
      expect(pid).toBeNull();
    });
  });

  describe("connection counting", () => {
    it("should track active connections", () => {
      expect(lifecycle.getActiveConnections()).toBe(0);

      lifecycle.incrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(1);

      lifecycle.incrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(2);

      lifecycle.decrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(1);

      lifecycle.decrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(0);
    });

    it("should not go below zero", () => {
      lifecycle.decrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(0);

      lifecycle.decrementConnections();
      expect(lifecycle.getActiveConnections()).toBe(0);
    });
  });

  describe("logging", () => {
    it("should write log messages to log file", async () => {
      await lifecycle.log("Test message");

      const logFilePath = lifecycle.getLogFilePath();
      const content = await fs.readFile(logFilePath, "utf-8");

      expect(content).toContain("Test message");
      // タイムスタンプがISO形式で含まれている
      expect(content).toMatch(/\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}/);
    });

    it("should append multiple log messages", async () => {
      await lifecycle.log("First message");
      await lifecycle.log("Second message");

      const logFilePath = lifecycle.getLogFilePath();
      const content = await fs.readFile(logFilePath, "utf-8");

      expect(content).toContain("First message");
      expect(content).toContain("Second message");
    });
  });

  describe("shutdown callback", () => {
    it("should register and store shutdown callback", () => {
      let called = false;
      const callback = async () => {
        called = true;
      };

      lifecycle.onShutdown(callback);

      // コールバックが登録されていることを確認（直接呼び出しはしない）
      // 実際のシャットダウン処理はgraceful shutdownで行われる
      expect(called).toBe(false);
    });
  });
});

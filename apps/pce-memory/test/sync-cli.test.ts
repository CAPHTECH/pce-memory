/**
 * CLI Tests for Sync Commands (Issue #18 Phase 3)
 *
 * CLIコマンドの引数パースとヘルプ出力をテスト
 */
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { runSyncCommand } from '../src/cli/sync.js';

// DB初期化などをモック
vi.mock('../src/db/connection.js', () => ({
  initDb: vi.fn().mockResolvedValue(undefined),
  initSchema: vi.fn().mockResolvedValue(undefined),
}));

vi.mock('../src/store/rate.js', () => ({
  initRateState: vi.fn().mockResolvedValue(undefined),
}));

vi.mock('../src/state/memoryState.js', () => ({
  initMemoryState: vi.fn().mockReturnValue(() => Promise.resolve({ _tag: 'Right', right: undefined })),
}));

// executePush/Pull/Statusをモック
vi.mock('../src/sync/push.js', () => ({
  executePush: vi.fn().mockResolvedValue({
    _tag: 'Right',
    right: {
      exported: { claims: 5, entities: 3, relations: 2 },
    },
  }),
}));

vi.mock('../src/sync/pull.js', () => ({
  executePull: vi.fn().mockResolvedValue({
    _tag: 'Right',
    right: {
      imported: {
        claims: { new: 3, updated: 1 },
        entities: { new: 2, updated: 0 },
        relations: { new: 1, updated: 0 },
      },
      conflicts: {
        conflicts: [],
        autoResolved: 0,
        skipped: 0,
      },
    },
  }),
}));

vi.mock('../src/sync/status.js', () => ({
  executeStatus: vi.fn().mockResolvedValue({
    _tag: 'Right',
    right: {
      exists: true,
      files: { claims: 5, entities: 3, relations: 2 },
      manifest: {
        version: '1.0.0',
        pce_memory_version: '0.6.0',
        last_push_at: '2025-01-10T10:00:00.000Z',
      },
      validation: { valid: true, errors: [] },
    },
  }),
}));

describe('runSyncCommand', () => {
  let consoleLogSpy: ReturnType<typeof vi.spyOn>;
  let consoleErrorSpy: ReturnType<typeof vi.spyOn>;

  beforeEach(() => {
    consoleLogSpy = vi.spyOn(console, 'log').mockImplementation(() => {});
    consoleErrorSpy = vi.spyOn(console, 'error').mockImplementation(() => {});
  });

  afterEach(() => {
    consoleLogSpy.mockRestore();
    consoleErrorSpy.mockRestore();
  });

  describe('help', () => {
    it('--helpでヘルプを表示', async () => {
      const exitCode = await runSyncCommand(['--help']);
      expect(exitCode).toBe(0);
      expect(consoleLogSpy).toHaveBeenCalled();
      const output = consoleLogSpy.mock.calls.map((c) => c[0]).join('\n');
      expect(output).toContain('pce-memory sync');
      expect(output).toContain('push');
      expect(output).toContain('pull');
      expect(output).toContain('status');
    });

    it('-hでヘルプを表示', async () => {
      const exitCode = await runSyncCommand(['-h']);
      expect(exitCode).toBe(0);
    });

    it('引数なしでヘルプを表示', async () => {
      const exitCode = await runSyncCommand([]);
      expect(exitCode).toBe(0);
    });
  });

  describe('unknown subcommand', () => {
    it('不明なサブコマンドでエラー', async () => {
      const exitCode = await runSyncCommand(['unknown']);
      expect(exitCode).toBe(1);
      expect(consoleErrorSpy).toHaveBeenCalledWith(expect.stringContaining('Unknown subcommand'));
    });
  });

  describe('push', () => {
    it('pushコマンドを実行', async () => {
      const exitCode = await runSyncCommand(['push']);
      expect(exitCode).toBe(0);
      expect(consoleLogSpy).toHaveBeenCalledWith(expect.stringContaining('Exported'));
    });

    it('--target-dirオプションを受け付ける', async () => {
      const { executePush } = await import('../src/sync/push.js');
      await runSyncCommand(['push', '--target-dir', 'custom-dir']);
      expect(executePush).toHaveBeenCalledWith(
        expect.objectContaining({ targetDir: 'custom-dir' })
      );
    });

    it('--scope-filterオプションを受け付ける', async () => {
      const { executePush } = await import('../src/sync/push.js');
      await runSyncCommand(['push', '--scope-filter', 'project,principle']);
      expect(executePush).toHaveBeenCalledWith(
        expect.objectContaining({ scopeFilter: ['project', 'principle'] })
      );
    });

    it('--boundary-filterオプションを受け付ける', async () => {
      const { executePush } = await import('../src/sync/push.js');
      await runSyncCommand(['push', '--boundary-filter', 'public,internal']);
      expect(executePush).toHaveBeenCalledWith(
        expect.objectContaining({ boundaryFilter: ['public', 'internal'] })
      );
    });
  });

  describe('pull', () => {
    it('pullコマンドを実行', async () => {
      const exitCode = await runSyncCommand(['pull']);
      expect(exitCode).toBe(0);
      expect(consoleLogSpy).toHaveBeenCalledWith(expect.stringContaining('Imported'));
    });

    it('--source-dirオプションを受け付ける', async () => {
      const { executePull } = await import('../src/sync/pull.js');
      await runSyncCommand(['pull', '--source-dir', 'custom-source']);
      expect(executePull).toHaveBeenCalledWith(
        expect.objectContaining({ sourceDir: 'custom-source' })
      );
    });

    it('--dry-runオプションを受け付ける', async () => {
      const { executePull } = await import('../src/sync/pull.js');
      await runSyncCommand(['pull', '--dry-run']);
      expect(executePull).toHaveBeenCalledWith(expect.objectContaining({ dryRun: true }));
      expect(consoleLogSpy).toHaveBeenCalledWith(expect.stringContaining('dry-run'));
    });
  });

  describe('status', () => {
    it('statusコマンドを実行', async () => {
      const exitCode = await runSyncCommand(['status']);
      expect(exitCode).toBe(0);
      expect(consoleLogSpy).toHaveBeenCalledWith(expect.stringContaining('Sync directory'));
    });

    it('--target-dirオプションを受け付ける', async () => {
      const { executeStatus } = await import('../src/sync/status.js');
      await runSyncCommand(['status', '--target-dir', 'custom-status']);
      expect(executeStatus).toHaveBeenCalledWith(
        expect.objectContaining({ targetDir: 'custom-status' })
      );
    });
  });
});

describe('expandTilde', () => {
  // expandTildeはsync.ts内のプライベート関数なので、CLIコマンド経由でテスト
  it('~/で始まるパスを展開', async () => {
    const { executePush } = await import('../src/sync/push.js');
    await runSyncCommand(['push', '--target-dir', '~/test-dir']);
    expect(executePush).toHaveBeenCalledWith(
      expect.objectContaining({
        targetDir: expect.stringMatching(/^\/.*test-dir$/),
      })
    );
  });
});

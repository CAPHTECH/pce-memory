/**
 * Sync Status機能テスト (Issue #18 Phase 2)
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import { executeStatus } from '../src/sync/status.js';
import { executePush } from '../src/sync/push.js';
import { upsertClaim } from '../src/store/claims.js';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { resetMemoryState } from '../src/state/memoryState.js';

describe('executeStatus', () => {
  let tempDir: string;

  beforeEach(async () => {
    // テスト用の一時ディレクトリを作成
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-status-test-'));
    // DB初期化
    await resetDbAsync();
    resetMemoryState();
    process.env.PCE_DB = ':memory:';
    process.env.PCE_RATE_CAP = '100';
    await initDb();
    await initSchema();
    await initRateState();
    await resetRates();
  });

  afterEach(async () => {
    // 一時ディレクトリを削除
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  it('ディレクトリが存在しない場合はexists: false', async () => {
    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exists).toBe(false);
      expect(result.right.files.claims).toBe(0);
      expect(result.right.files.entities).toBe(0);
      expect(result.right.files.relations).toBe(0);
      expect(result.right.validation.isValid).toBe(true);
    }
  });

  it('空のディレクトリではfiles全て0', async () => {
    // 空の.pce-sharedディレクトリを作成
    const syncDir = path.join(tempDir, '.pce-shared');
    await fs.mkdir(syncDir, { recursive: true });

    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exists).toBe(true);
      expect(result.right.files.claims).toBe(0);
      expect(result.right.files.entities).toBe(0);
      expect(result.right.files.relations).toBe(0);
    }
  });

  it('manifest.jsonの内容を正しく返す', async () => {
    // Pushを実行してmanifest.jsonを作成
    const text = 'テスト用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: hash,
    });

    await executePush({ basePath: tempDir });

    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exists).toBe(true);
      expect(result.right.manifest).toBeDefined();
      expect(result.right.manifest?.version).toBe('1.0');
      expect(result.right.manifest?.pce_memory_version).toBeDefined();
      expect(result.right.manifest?.last_push_at).toBeDefined();
    }
  });

  it('Claims/Entities/Relationsのファイル数を正しくカウント', async () => {
    // 複数のClaimを作成してPush
    for (let i = 0; i < 3; i++) {
      const text = `テスト用Claim ${i}`;
      const hash = `sha256:${computeContentHash(text)}`;

      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });
    }

    await executePush({ basePath: tempDir });

    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.files.claims).toBe(3);
    }
  });

  it('無効なmanifestはvalidation.errorsに含まれる', async () => {
    // .pce-sharedディレクトリを作成
    const syncDir = path.join(tempDir, '.pce-shared');
    await fs.mkdir(syncDir, { recursive: true });

    // 無効なmanifest.jsonを作成
    const manifestPath = path.join(syncDir, 'manifest.json');
    await fs.writeFile(manifestPath, JSON.stringify({ invalid: true }), 'utf-8');

    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exists).toBe(true);
      expect(result.right.validation.isValid).toBe(false);
      expect(result.right.validation.errors.length).toBeGreaterThan(0);
    }
  });

  it('last_pull_atがあれば返す', async () => {
    // .pce-sharedディレクトリとmanifest.jsonを作成
    const syncDir = path.join(tempDir, '.pce-shared');
    await fs.mkdir(syncDir, { recursive: true });

    const manifest = {
      version: '1.0',
      pce_memory_version: '0.7.0',
      last_push_at: new Date().toISOString(),
      last_pull_at: '2025-12-12T10:00:00.000Z',
    };
    const manifestPath = path.join(syncDir, 'manifest.json');
    await fs.writeFile(manifestPath, JSON.stringify(manifest, null, 2), 'utf-8');

    const result = await executeStatus({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.manifest).toBeDefined();
      expect(result.right.manifest?.last_pull_at).toBe('2025-12-12T10:00:00.000Z');
    }
  });

  it('target_dirオプションで別のディレクトリを指定可能', async () => {
    // カスタムディレクトリを作成
    const customDir = 'custom-sync-dir';
    const syncDir = path.join(tempDir, customDir);
    await fs.mkdir(syncDir, { recursive: true });

    const result = await executeStatus({ basePath: tempDir, targetDir: customDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exists).toBe(true);
      expect(result.right.targetDir).toContain(customDir);
    }
  });

  it('パストラバーサル攻撃を防止', async () => {
    const result = await executeStatus({ basePath: tempDir, targetDir: '../../../etc' });

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('SYNC_PATH_ERROR');
    }
  });
});

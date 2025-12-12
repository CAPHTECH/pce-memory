/**
 * Push機能テスト (Issue #18)
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import packageJson from '../package.json' with { type: 'json' };
import { executePush } from '../src/sync/push.js';
import { upsertClaim } from '../src/store/claims.js';
import { upsertEntity } from '../src/store/entities.js';
import { upsertRelation } from '../src/store/relations.js';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { resetMemoryState } from '../src/state/memoryState.js';

describe('executePush', () => {
  let tempDir: string;

  beforeEach(async () => {
    // テスト用の一時ディレクトリを作成
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-test-'));
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

  it('空のDBでは何もエクスポートしない', async () => {
    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(0);
      expect(result.right.exported.entities).toBe(0);
      expect(result.right.exported.relations).toBe(0);
    }
  });

  it('projectスコープのClaimをエクスポート', async () => {
    const text = 'テスト用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: hash,
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(1);

      // ファイルが作成されているか確認
      const claimFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${hash.replace('sha256:', '')}.json`
      );
      const exists = await fs
        .access(claimFile)
        .then(() => true)
        .catch(() => false);
      expect(exists).toBe(true);
    }
  });

  it('sessionスコープはデフォルトでエクスポートしない', async () => {
    const text = 'セッション用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: hash,
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(0);
    }
  });

  it('secretはエクスポートしない', async () => {
    const text = '機密Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: hash,
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(0);
    }
  });

  it('piiはデフォルトでエクスポートしない（オプトイン）', async () => {
    const text = 'PII含むClaim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'pii',
      content_hash: hash,
    });

    // デフォルトではpiiはエクスポートされない
    const result = await executePush({ basePath: tempDir });
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(0);
    }

    // 明示的にpiiを指定した場合はエクスポートされる
    const resultWithPii = await executePush({
      basePath: tempDir,
      boundaryFilter: ['public', 'internal', 'pii'],
    });
    expect(E.isRight(resultWithPii)).toBe(true);
    if (E.isRight(resultWithPii)) {
      expect(resultWithPii.right.exported.claims).toBe(1);
    }
  });

  it('Claimに関連付けられていないEntityはエクスポートしない', async () => {
    // EntityをClaimと関連付けずに単独で作成
    await upsertEntity({
      id: 'ent_test123',
      type: 'Concept',
      name: 'テストエンティティ',
    });

    const result = await executePush({
      basePath: tempDir,
      includeEntities: true,
    });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // Claimに関連付けられていないのでエクスポートされない
      expect(result.right.exported.entities).toBe(0);
    }
  });

  it('Claimに関連付けられていないRelationはエクスポートしない', async () => {
    // EntityをClaimと関連付けずに作成
    await upsertEntity({ id: 'ent_a', type: 'Concept', name: 'Entity A' });
    await upsertEntity({ id: 'ent_b', type: 'Concept', name: 'Entity B' });

    await upsertRelation({
      id: 'rel_test123',
      src_id: 'ent_a',
      dst_id: 'ent_b',
      type: 'KNOWS',
    });

    const result = await executePush({
      basePath: tempDir,
      includeRelations: true,
    });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // 関連するEntityがエクスポートされていないのでRelationもエクスポートされない
      expect(result.right.exported.relations).toBe(0);
    }
  });

  it('manifest.jsonが作成される', async () => {
    const text = 'テスト用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: hash,
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.manifestUpdated).toBe(true);

      // manifest.jsonの内容を確認
      const manifestPath = path.join(tempDir, '.pce-shared', 'manifest.json');
      const manifestContent = await fs.readFile(manifestPath, 'utf-8');
      const manifest = JSON.parse(manifestContent);
      expect(manifest.version).toBe('1.0');
      expect(manifest.pce_memory_version).toBe(packageJson.version);
      expect(manifest.last_push_at).toBeDefined();
    }
  });

  it('カスタムターゲットディレクトリを指定', async () => {
    const text = 'テスト用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: hash,
    });

    const result = await executePush({
      basePath: tempDir,
      targetDir: '.custom-sync',
    });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.targetDir).toContain('.custom-sync');

      // カスタムディレクトリにファイルが作成されているか確認
      const manifestPath = path.join(tempDir, '.custom-sync', 'manifest.json');
      const exists = await fs
        .access(manifestPath)
        .then(() => true)
        .catch(() => false);
      expect(exists).toBe(true);
    }
  });
});

/**
 * Pull機能テスト (Issue #18)
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import { executePull } from '../src/sync/pull.js';
import { executePush } from '../src/sync/push.js';
import { upsertClaim, findClaimByContentHash } from '../src/store/claims.js';
import { findEntityById } from '../src/store/entities.js';
import { findRelationById } from '../src/store/relations.js';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import type { ClaimExport, EntityExport, RelationExport } from '../src/sync/schemas.js';

describe('executePull', () => {
  let tempDir: string;
  let syncDir: string;

  beforeEach(async () => {
    // テスト用の一時ディレクトリを作成
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-test-'));
    syncDir = path.join(tempDir, '.pce-shared');

    // .pce-shared ディレクトリ構造を作成
    await fs.mkdir(path.join(syncDir, 'claims', 'project'), { recursive: true });
    await fs.mkdir(path.join(syncDir, 'claims', 'principle'), { recursive: true });
    await fs.mkdir(path.join(syncDir, 'entities'), { recursive: true });
    await fs.mkdir(path.join(syncDir, 'relations'), { recursive: true });

    // manifest.jsonを作成
    await fs.writeFile(
      path.join(syncDir, 'manifest.json'),
      JSON.stringify({
        version: '1.0',
        pce_memory_version: '0.7.0',
        last_push_at: new Date().toISOString(),
      })
    );

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

  it('空のディレクトリからは何もインポートしない', async () => {
    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.entities.new).toBe(0);
      expect(result.right.imported.relations.new).toBe(0);
    }
  });

  it('有効なClaimをインポート', async () => {
    const text = 'インポートテスト用Claim';
    const hash = computeContentHash(text);

    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(1);

      // DBに保存されているか確認
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved).toBeDefined();
      expect(saved?.text).toBe(text);
    }
  });

  it('content_hashが不一致の場合はバリデーションエラー', async () => {
    const text = 'テスト用Claim';
    const wrongHash = '0000000000000000000000000000000000000000000000000000000000000000';

    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${wrongHash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${wrongHash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.validationErrors.length).toBeGreaterThan(0);
      expect(result.right.validationErrors[0]?.error).toContain('Content hash mismatch');
    }
  });

  it('重複Claimはスキップ', async () => {
    const text = '重複テスト用Claim';
    const hash = computeContentHash(text);

    // 先にDBに登録
    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    });

    // 同じClaimをファイルに配置
    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
    }
  });

  it('boundary_classの格上げ', async () => {
    const text = '格上げテスト用Claim';
    const hash = computeContentHash(text);

    // publicで登録
    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'public',
      content_hash: `sha256:${hash}`,
    });

    // internalとしてpull（格上げ）
    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.upgradedBoundary).toBe(1);

      // DBで確認
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved?.boundary_class).toBe('internal');
    }
  });

  it('boundary_classの格下げは防止', async () => {
    const text = '格下げ防止テスト用Claim';
    const hash = computeContentHash(text);

    // internalで登録
    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    });

    // publicとしてpull（格下げは無視）
    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'public',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.upgradedBoundary).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);

      // DBで確認（internalのまま）
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved?.boundary_class).toBe('internal');
    }
  });

  it('Entityをインポート', async () => {
    const entity: EntityExport = {
      id: 'ent_pull_test',
      type: 'Concept',
      name: 'プルテストエンティティ',
    };

    await fs.writeFile(path.join(syncDir, 'entities', 'ent_pull_test.json'), JSON.stringify(entity));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.entities.new).toBe(1);

      // DBに保存されているか確認
      const saved = await findEntityById('ent_pull_test');
      expect(saved).toBeDefined();
      expect(saved?.name).toBe('プルテストエンティティ');
    }
  });

  it('Relationをインポート', async () => {
    // 先にEntityを作成
    const entityA: EntityExport = { id: 'ent_a', type: 'Concept', name: 'Entity A' };
    const entityB: EntityExport = { id: 'ent_b', type: 'Concept', name: 'Entity B' };

    await fs.writeFile(path.join(syncDir, 'entities', 'ent_a.json'), JSON.stringify(entityA));
    await fs.writeFile(path.join(syncDir, 'entities', 'ent_b.json'), JSON.stringify(entityB));

    const relation: RelationExport = {
      id: 'rel_pull_test',
      src_id: 'ent_a',
      dst_id: 'ent_b',
      type: 'KNOWS',
    };

    await fs.writeFile(path.join(syncDir, 'relations', 'rel_pull_test.json'), JSON.stringify(relation));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.relations.new).toBe(1);

      // DBに保存されているか確認
      const saved = await findRelationById('rel_pull_test');
      expect(saved).toBeDefined();
      expect(saved?.type).toBe('KNOWS');
    }
  });

  it('dryRunモードではDBに書き込まない', async () => {
    const text = 'ドライランテスト用Claim';
    const hash = computeContentHash(text);

    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir, dryRun: true });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(1);
      expect(result.right.dryRun).toBe(true);

      // DBには保存されていない
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved).toBeUndefined();
    }
  });

  it('secretはインポートしない', async () => {
    const text = '機密テスト用Claim';
    const hash = computeContentHash(text);

    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(path.join(syncDir, 'claims', 'project', `${hash}.json`), JSON.stringify(claim));

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1); // secretはスキップ扱い
    }
  });

  it('無効なJSONスキーマはバリデーションエラー', async () => {
    // kindが無効
    const invalidClaim = {
      text: 'テスト',
      kind: 'invalid_kind',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:0000000000000000000000000000000000000000000000000000000000000000',
    };

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', '0000000000000000000000000000000000000000000000000000000000000000.json'),
      JSON.stringify(invalidClaim)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.validationErrors.length).toBeGreaterThan(0);
    }
  });

  it('ソースディレクトリが存在しない場合はエラー', async () => {
    const result = await executePull({ basePath: '/nonexistent/path' });

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('SYNC_PULL_FAILED');
    }
  });
});

describe('Push-Pull往復テスト', () => {
  let tempDir: string;

  beforeEach(async () => {
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-roundtrip-'));
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
    await fs.rm(tempDir, { recursive: true, force: true });
  });

  it('Push後にPullしても重複なし', async () => {
    const text = '往復テスト用Claim';
    const hash = `sha256:${computeContentHash(text)}`;

    // Claimを登録
    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: hash,
    });

    // Push
    const pushResult = await executePush({ basePath: tempDir });
    expect(E.isRight(pushResult)).toBe(true);

    // 同じDBにPull
    const pullResult = await executePull({ basePath: tempDir });
    expect(E.isRight(pullResult)).toBe(true);
    if (E.isRight(pullResult)) {
      // 既存のClaimなので重複としてスキップされる
      expect(pullResult.right.imported.claims.new).toBe(0);
      expect(pullResult.right.imported.claims.skippedDuplicate).toBe(1);
    }
  });
});

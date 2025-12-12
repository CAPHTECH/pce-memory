/**
 * Incremental Sync機能テスト (Issue #18 Phase 2)
 *
 * sinceパラメータによる増分同期とManifest更新のテスト
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as os from 'node:os';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import { executePush } from '../src/sync/push.js';
import { executePull } from '../src/sync/pull.js';
import { upsertClaim } from '../src/store/claims.js';
import { upsertEntity, linkClaimEntity } from '../src/store/entities.js';
import { upsertRelation } from '../src/store/relations.js';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import type { Manifest } from '../src/sync/schemas.js';

describe('Incremental Sync (since parameter)', () => {
  let tempDir: string;

  beforeEach(async () => {
    // テスト用の一時ディレクトリを作成
    tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-incremental-test-'));
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

  describe('Push with since parameter', () => {
    it('Pushのsinceはcreated_at（DB挿入時刻）でフィルタする', async () => {
      // Push sinceはDB内のcreated_atでフィルタする
      // 未来日時を指定すれば、全Claimがフィルタされる

      const text = 'テストClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      // 未来の日時を指定してPush
      const futureDate = new Date('2099-01-01T00:00:00.000Z');
      const result = await executePush({ basePath: tempDir, since: futureDate });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        // 全てのClaimがsinceより前に作成されているので0
        expect(result.right.exported.claims).toBe(0);
      }
    });

    it('sinceなしで全Claimをエクスポート', async () => {
      // 複数のClaimを作成
      for (let i = 0; i < 3; i++) {
        const text = `Claim ${i}`;
        const hash = `sha256:${computeContentHash(text)}`;
        await upsertClaim({
          text,
          kind: 'fact',
          scope: 'project',
          boundary_class: 'internal',
          content_hash: hash,
          provenance: {
            at: new Date(Date.now() - i * 86400000).toISOString(), // 日ごとにずらす
          },
        });
      }

      const result = await executePush({ basePath: tempDir });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        expect(result.right.exported.claims).toBe(3);
      }
    });

    it('Claimに関連するEntities/Relationsがエクスポートされる', async () => {
      // Entityを作成
      await upsertEntity({
        id: 'entity-1',
        type: 'Concept',
        name: 'テストEntity',
      });

      await upsertEntity({
        id: 'entity-2',
        type: 'Concept',
        name: 'テストEntity2',
      });

      // Relationを作成
      await upsertRelation({
        id: 'relation-1',
        src_id: 'entity-1',
        dst_id: 'entity-2',
        type: 'RELATED_TO',
      });

      // Claimを作成
      const text = 'テストClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      const { claim } = await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      // ClaimとEntityをリンク
      await linkClaimEntity(claim.id, 'entity-1');
      await linkClaimEntity(claim.id, 'entity-2');

      // Pushを実行
      const result = await executePush({ basePath: tempDir });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        // Claimに関連するEntityとRelationがエクスポートされる
        expect(result.right.exported.claims).toBe(1);
        expect(result.right.exported.entities).toBe(2);
        expect(result.right.exported.relations).toBe(1);
      }
    });
  });

  describe('Pull with since parameter', () => {
    it('sinceより新しいClaimのみをインポート', async () => {
      // まず複数のClaimをPush
      const oldText = '古いClaim';
      const oldHash = `sha256:${computeContentHash(oldText)}`;
      await upsertClaim({
        text: oldText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: oldHash,
        provenance: {
          at: '2025-01-01T00:00:00.000Z',
        },
      });

      const newText = '新しいClaim';
      const newHash = `sha256:${computeContentHash(newText)}`;
      await upsertClaim({
        text: newText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: newHash,
        provenance: {
          at: '2025-06-01T00:00:00.000Z',
        },
      });

      await executePush({ basePath: tempDir });

      // DBをリセット（新しい環境をシミュレート）
      await resetDbAsync();
      resetMemoryState();
      await initDb();
      await initSchema();
      await initRateState();
      await resetRates();

      // sinceを指定してPull
      const since = new Date('2025-03-01T00:00:00.000Z');
      const result = await executePull({ basePath: tempDir, since });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        expect(result.right.imported.claims.new).toBe(1);
        expect(result.right.imported.claims.skippedBySince).toBe(1);
      }
    });

    it('provenance.atがないClaimはsinceでスキップされない', async () => {
      // provenanceなしのClaimを作成
      const text = 'provenanceなしClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      await executePush({ basePath: tempDir });

      // DBをリセット
      await resetDbAsync();
      resetMemoryState();
      await initDb();
      await initSchema();
      await initRateState();
      await resetRates();

      // sinceを指定してPull
      const since = new Date('2025-03-01T00:00:00.000Z');
      const result = await executePull({ basePath: tempDir, since });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        // provenance.atがないのでスキップされない
        expect(result.right.imported.claims.new).toBe(1);
        expect(result.right.imported.claims.skippedBySince).toBe(0);
      }
    });
  });

  describe('Manifest auto-update', () => {
    it('Pull後にmanifest.jsonのlast_pull_atが更新される', async () => {
      // Claimを作成してPush
      const text = 'テストClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      await executePush({ basePath: tempDir });

      // Pull実行前のmanifestを確認
      const manifestPath = path.join(tempDir, '.pce-shared', 'manifest.json');
      const beforeManifest = JSON.parse(await fs.readFile(manifestPath, 'utf-8')) as Manifest;
      expect(beforeManifest.last_pull_at).toBeUndefined();

      // DBをリセット
      await resetDbAsync();
      resetMemoryState();
      await initDb();
      await initSchema();
      await initRateState();
      await resetRates();

      // Pull実行
      const result = await executePull({ basePath: tempDir });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        expect(result.right.manifestUpdated).toBe(true);
      }

      // Pull実行後のmanifestを確認
      const afterManifest = JSON.parse(await fs.readFile(manifestPath, 'utf-8')) as Record<
        string,
        unknown
      >;
      expect(afterManifest.last_pull_at).toBeDefined();
      expect(typeof afterManifest.last_pull_at).toBe('string');
    });

    it('dryRun時はmanifestが更新されない', async () => {
      // Claimを作成してPush
      const text = 'テストClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      await executePush({ basePath: tempDir });

      // DBをリセット
      await resetDbAsync();
      resetMemoryState();
      await initDb();
      await initSchema();
      await initRateState();
      await resetRates();

      // dryRun: true でPull実行
      const result = await executePull({ basePath: tempDir, dryRun: true });

      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        expect(result.right.manifestUpdated).toBe(false);
      }

      // manifestのlast_pull_atは更新されていない
      const manifestPath = path.join(tempDir, '.pce-shared', 'manifest.json');
      const manifest = JSON.parse(await fs.readFile(manifestPath, 'utf-8')) as Manifest;
      expect(manifest.last_pull_at).toBeUndefined();
    });

    it('Push時にlast_push_atが記録される', async () => {
      const text = 'テストClaim';
      const hash = `sha256:${computeContentHash(text)}`;
      await upsertClaim({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash,
      });

      const beforePush = new Date();
      await executePush({ basePath: tempDir });
      const afterPush = new Date();

      const manifestPath = path.join(tempDir, '.pce-shared', 'manifest.json');
      const manifest = JSON.parse(await fs.readFile(manifestPath, 'utf-8')) as Manifest;

      expect(manifest.last_push_at).toBeDefined();
      const pushTime = new Date(manifest.last_push_at);
      expect(pushTime.getTime()).toBeGreaterThanOrEqual(beforePush.getTime());
      expect(pushTime.getTime()).toBeLessThanOrEqual(afterPush.getTime());
    });
  });

  describe('Incremental workflow', () => {
    it('Push → Pull → 追加Push → 増分Pullのワークフロー', async () => {
      // Step 1: 初回Push
      const text1 = 'Claim 1';
      const hash1 = `sha256:${computeContentHash(text1)}`;
      await upsertClaim({
        text: text1,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash1,
        provenance: { at: '2025-01-01T00:00:00.000Z' },
      });

      await executePush({ basePath: tempDir });

      // Step 2: Pull（別環境をシミュレート）
      await resetDbAsync();
      resetMemoryState();
      await initDb();
      await initSchema();
      await initRateState();
      await resetRates();

      const pull1 = await executePull({ basePath: tempDir });
      expect(E.isRight(pull1)).toBe(true);
      if (E.isRight(pull1)) {
        expect(pull1.right.imported.claims.new).toBe(1);
      }

      // Step 3: 追加Claimを作成してPush
      const text2 = 'Claim 2';
      const hash2 = `sha256:${computeContentHash(text2)}`;
      await upsertClaim({
        text: text2,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hash2,
        provenance: { at: '2025-06-01T00:00:00.000Z' },
      });

      await executePush({ basePath: tempDir });

      // Step 4: 増分Pull（sinceを使用）
      // Note: Claim 2はStep 3でローカルDBに追加されているため、Pullでは重複としてスキップされる
      const since = new Date('2025-03-01T00:00:00.000Z');
      const pull2 = await executePull({ basePath: tempDir, since });

      expect(E.isRight(pull2)).toBe(true);
      if (E.isRight(pull2)) {
        // Claim 2はローカルDBに既に存在するため重複としてスキップ
        expect(pull2.right.imported.claims.new).toBe(0);
        expect(pull2.right.imported.claims.skippedDuplicate).toBe(1);
        // Claim 1はsinceより古いためスキップ
        expect(pull2.right.imported.claims.skippedBySince).toBe(1);
      }
    });
  });
});

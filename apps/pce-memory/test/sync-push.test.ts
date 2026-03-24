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
import { upsertClaim, markClaimRolledBack } from '../src/store/claims.js';
import { upsertEntity } from '../src/store/entities.js';
import { upsertRelation } from '../src/store/relations.js';
import { insertPromotionQueueRow } from '../src/store/promotionQueue.js';
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

  it('memory_type を含むClaimをエクスポート', async () => {
    const text = 'memory type付きClaim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: hash,
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      const claimFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${hash.replace('sha256:', '')}.json`
      );
      const claimContent = JSON.parse(await fs.readFile(claimFile, 'utf-8')) as {
        memory_type?: string;
      };
      expect(claimContent.memory_type).toBe('knowledge');
    }
  });

  it('sessionスコープは明示指定してもエクスポートしない', async () => {
    const sessionText = 'セッション用Claim';
    const sessionHash = `sha256:${computeContentHash(sessionText)}`;
    const projectText = 'project scope claim';
    const projectHash = `sha256:${computeContentHash(projectText)}`;

    await upsertClaim({
      text: sessionText,
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: sessionHash,
    });

    await upsertClaim({
      text: projectText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: projectHash,
    });

    const result = await executePush({
      basePath: tempDir,
      scopeFilter: ['session', 'project'],
    });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(1);

      const sessionFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'session',
        `${sessionHash.replace('sha256:', '')}.json`
      );
      const projectFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${projectHash.replace('sha256:', '')}.json`
      );

      const sessionExists = await fs
        .access(sessionFile)
        .then(() => true)
        .catch(() => false);
      const projectExists = await fs
        .access(projectFile)
        .then(() => true)
        .catch(() => false);

      expect(sessionExists).toBe(false);
      expect(projectExists).toBe(true);
    }
  });

  it('tombstone または rollback 済みのClaimをエクスポートしない', async () => {
    const active = await upsertClaim({
      text: 'active claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash('active claim')}`,
    });
    const tombstoned = await upsertClaim({
      text: 'tombstoned claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash('tombstoned claim')}`,
    });
    const rolledBack = await upsertClaim({
      text: 'rolled back claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash('rolled back claim')}`,
    });

    await markClaimRolledBack(tombstoned.claim.id, {
      tombstone_at: '2026-03-24T00:00:00.000Z',
      rollback_reason: 'test tombstone',
      superseded_by: 'rbk_test_tombstone',
    });
    await insertPromotionQueueRow({
      id: 'rbk_sync_skip',
      source_layer: 'meso',
      target_layer: 'meso',
      source_ids: JSON.stringify([rolledBack.claim.id]),
      distilled_text: rolledBack.claim.text,
      candidate_hash: `sha256:${computeContentHash('rollback marker for sync push test')}`,
      proposed_kind: rolledBack.claim.kind,
      proposed_scope: rolledBack.claim.scope,
      proposed_boundary_class: rolledBack.claim.boundary_class,
      proposed_memory_type: rolledBack.claim.memory_type ?? null,
      provenance: JSON.stringify({
        rollback_of: rolledBack.claim.id,
        actor: 'vitest',
      }),
      evidence_ids: JSON.stringify([]),
      policy_version_checked: 'test-policy',
      boundary_check_result: JSON.stringify({ allowed: true, rollback: true }),
      status: 'rolled_back',
      created_at: '2026-03-24T00:00:00.000Z',
      resolved_at: '2026-03-24T00:00:00.000Z',
      accepted_claim_id: rolledBack.claim.id,
      rejected_reason: 'test rollback',
    });

    const result = await executePush({ basePath: tempDir, scopeFilter: ['project'] });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(1);

      const activeFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${active.claim.content_hash.replace('sha256:', '')}.json`
      );
      const tombstonedFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${tombstoned.claim.content_hash.replace('sha256:', '')}.json`
      );
      const rolledBackFile = path.join(
        tempDir,
        '.pce-shared',
        'claims',
        'project',
        `${rolledBack.claim.content_hash.replace('sha256:', '')}.json`
      );

      const activeExists = await fs
        .access(activeFile)
        .then(() => true)
        .catch(() => false);
      const tombstonedExists = await fs
        .access(tombstonedFile)
        .then(() => true)
        .catch(() => false);
      const rolledBackExists = await fs
        .access(rolledBackFile)
        .then(() => true)
        .catch(() => false);

      expect(activeExists).toBe(true);
      expect(tombstonedExists).toBe(false);
      expect(rolledBackExists).toBe(false);
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

  it('promotion_queue は sync 対象に含めない', async () => {
    await insertPromotionQueueRow({
      id: 'pq_local_only',
      source_layer: 'micro',
      target_layer: 'meso',
      source_ids: JSON.stringify(['obs_1']),
      distilled_text: 'local only candidate',
      candidate_hash: `sha256:${computeContentHash('local only candidate')}`,
      proposed_kind: 'fact',
      proposed_scope: 'project',
      proposed_boundary_class: 'internal',
      proposed_memory_type: 'knowledge',
      provenance: JSON.stringify({ actor: 'vitest', at: '2026-03-24T00:00:00.000Z' }),
      evidence_ids: JSON.stringify([]),
      policy_version_checked: 'test-policy',
      boundary_check_result: JSON.stringify({ allowed: true }),
      status: 'pending',
      created_at: '2026-03-24T00:00:00.000Z',
    });

    const result = await executePush({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.exported.claims).toBe(0);
      const promotionQueueDir = path.join(tempDir, '.pce-shared', 'promotion_queue');
      const exists = await fs
        .access(promotionQueueDir)
        .then(() => true)
        .catch(() => false);
      expect(exists).toBe(false);
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

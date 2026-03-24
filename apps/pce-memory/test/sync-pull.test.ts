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
import { markClaimRolledBack, upsertClaim, findClaimByContentHash } from '../src/store/claims.js';
import { findEntityById } from '../src/store/entities.js';
import { findRelationById } from '../src/store/relations.js';
import { insertPromotionQueueRow } from '../src/store/promotionQueue.js';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

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

  it('memory_type を含むClaimをインポート', async () => {
    const text = 'memory type import claim';
    const hash = computeContentHash(text);

    const claim: ClaimExport = {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'procedure',
      content_hash: `sha256:${hash}`,
    };

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved?.memory_type).toBe('procedure');
    }
  });

  it('session スコープのClaimは明示指定してもインポートしない', async () => {
    const text = 'session scope import';
    const hash = computeContentHash(text);

    await fs.mkdir(path.join(syncDir, 'claims', 'session'), { recursive: true });
    await fs.writeFile(
      path.join(syncDir, 'claims', 'session', `${hash}.json`),
      JSON.stringify({
        text,
        kind: 'fact',
        scope: 'session',
        boundary_class: 'internal',
        memory_type: 'working_state',
        content_hash: `sha256:${hash}`,
      } satisfies ClaimExport)
    );

    const result = await executePull({
      basePath: tempDir,
      scopeFilter: ['session', 'project'],
    });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(0);
      expect(await findClaimByContentHash(`sha256:${hash}`)).toBeUndefined();
    }
  });

  it('tombstone の付いたClaimは穏当にスキップする', async () => {
    const text = 'tombstoned import';
    const hash = computeContentHash(text);

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        content_hash: `sha256:${hash}`,
        tombstone: true,
        tombstone_at: '2026-03-24T00:00:00.000Z',
      } satisfies ClaimExport)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
      expect(result.right.validationErrors).toHaveLength(0);
      expect(await findClaimByContentHash(`sha256:${hash}`)).toBeUndefined();
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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${wrongHash}.json`),
      JSON.stringify(claim)
    );

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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
    }
  });

  it('重複Claimでも欠けている memory_type は backfill する', async () => {
    const text = 'duplicate with memory type backfill';
    const hash = computeContentHash(text);

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${hash}`,
    });

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'procedure',
        content_hash: `sha256:${hash}`,
      } satisfies ClaimExport)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved?.memory_type).toBe('procedure');
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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

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

  it('conflicting incoming memory_type does not overwrite the existing durable classification', async () => {
    const text = 'memory type conflict should keep local classification';
    const hash = computeContentHash(text);

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${hash}`,
    });

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'procedure',
        content_hash: `sha256:${hash}`,
      } satisfies ClaimExport)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
      expect(result.right.imported.claims.upgradedBoundary).toBe(0);
      const saved = await findClaimByContentHash(`sha256:${hash}`);
      expect(saved?.memory_type).toBe('knowledge');
    }
  });

  it('rolled-back local claims are skipped instead of being re-imported from sync files', async () => {
    const text = 'rolled back durable claim should stay rolled back';
    const hash = computeContentHash(text);

    const inserted = await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${hash}`,
    });

    await markClaimRolledBack(inserted.claim.id, {
      tombstone_at: '2026-03-24T00:00:00.000Z',
      rollback_reason: 'rollback before pull regression test',
      superseded_by: 'rbk_sync_pull',
    });
    await insertPromotionQueueRow({
      id: 'rbk_sync_pull',
      source_layer: 'meso',
      target_layer: 'meso',
      source_ids: JSON.stringify([inserted.claim.id]),
      distilled_text: inserted.claim.text,
      candidate_hash: `sha256:${computeContentHash('rollback marker for sync pull test')}`,
      proposed_kind: inserted.claim.kind,
      proposed_scope: inserted.claim.scope,
      proposed_boundary_class: inserted.claim.boundary_class,
      proposed_memory_type: inserted.claim.memory_type ?? null,
      provenance: JSON.stringify({
        rollback_of: inserted.claim.id,
        actor: 'vitest',
      }),
      evidence_ids: JSON.stringify([]),
      policy_version_checked: 'test-policy',
      boundary_check_result: JSON.stringify({ allowed: true, rollback: true }),
      status: 'rolled_back',
      created_at: '2026-03-24T00:00:00.000Z',
      resolved_at: '2026-03-24T00:00:00.000Z',
      accepted_claim_id: inserted.claim.id,
      rejected_reason: 'test rollback',
    });

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify({
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        content_hash: `sha256:${hash}`,
      } satisfies ClaimExport)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1);
      const conn = await getConnection();
      const reader = await conn.runAndReadAll(
        'SELECT COUNT(*)::INTEGER AS cnt FROM claims WHERE content_hash = $1',
        [`sha256:${hash}`]
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]?.cnt).toBe(1);
    }
  });

  it('Entityをインポート', async () => {
    const entity: EntityExport = {
      id: 'ent_pull_test',
      type: 'Concept',
      name: 'プルテストエンティティ',
    };

    await fs.writeFile(
      path.join(syncDir, 'entities', 'ent_pull_test.json'),
      JSON.stringify(entity)
    );

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

    await fs.writeFile(
      path.join(syncDir, 'relations', 'rel_pull_test.json'),
      JSON.stringify(relation)
    );

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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

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

    await fs.writeFile(
      path.join(syncDir, 'claims', 'project', `${hash}.json`),
      JSON.stringify(claim)
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.claims.skippedDuplicate).toBe(1); // secretはスキップ扱い
    }
  });

  it('promotion_queue ディレクトリは無視する', async () => {
    await fs.mkdir(path.join(syncDir, 'promotion_queue'), { recursive: true });
    await fs.writeFile(
      path.join(syncDir, 'promotion_queue', 'pq_local_only.json'),
      JSON.stringify({
        id: 'pq_local_only',
        source_layer: 'micro',
        target_layer: 'meso',
      })
    );

    const result = await executePull({ basePath: tempDir });

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.imported.claims.new).toBe(0);
      expect(result.right.imported.entities.new).toBe(0);
      expect(result.right.imported.relations.new).toBe(0);
      expect(result.right.validationErrors).toHaveLength(0);
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
      path.join(
        syncDir,
        'claims',
        'project',
        '0000000000000000000000000000000000000000000000000000000000000000.json'
      ),
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

  it('memory_type が push/pull round-trip で保持される', async () => {
    const text = 'roundtrip memory type claim';
    const hash = `sha256:${computeContentHash(text)}`;

    await upsertClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'procedure',
      content_hash: hash,
    });

    const pushResult = await executePush({ basePath: tempDir });
    expect(E.isRight(pushResult)).toBe(true);

    await resetDbAsync();
    resetMemoryState();
    process.env.PCE_DB = ':memory:';
    process.env.PCE_RATE_CAP = '100';
    await initDb();
    await initSchema();
    await initRateState();
    await resetRates();

    const pullResult = await executePull({ basePath: tempDir });
    expect(E.isRight(pullResult)).toBe(true);
    if (E.isRight(pullResult)) {
      expect(pullResult.right.imported.claims.new).toBe(1);
      const saved = await findClaimByContentHash(hash);
      expect(saved?.memory_type).toBe('procedure');
    }
  });
});

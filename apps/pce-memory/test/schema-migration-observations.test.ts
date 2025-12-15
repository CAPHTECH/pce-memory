import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { dispatchTool } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  await initDb();
});

describe('Schema migration: legacy observations', () => {
  it('旧observationsテーブルを検知して移行できる', async () => {
    const conn = await getConnection();

    // 旧スキーマ（docs/schema.md 想定の例）を先に作っておく
    await conn.run(`
      CREATE TABLE observations (
        id TEXT PRIMARY KEY,
        source_type TEXT NOT NULL,
        source_id TEXT,
        content TEXT NOT NULL,
        actor TEXT,
        tags TEXT,
        created_at INTEGER NOT NULL
      )
    `);
    await conn.run(
      'INSERT INTO observations (id, source_type, source_id, content, actor, tags, created_at) VALUES ($1,$2,$3,$4,$5,$6,$7)',
      ['legacy_1', 'chat', 'conv_1', 'legacy content', 'user', 'tag1,tag2', 1_700_000_000]
    );

    // initSchemaで新DDL＋マイグレーションが走る
    await initSchema();
    await initRateState();
    await resetRates();

    // 旧テーブルが退避されている
    const legacyTables = await conn.runAndReadAll(
      "SELECT table_name FROM information_schema.tables WHERE table_name LIKE 'observations_legacy_%'"
    );
    const legacyRows = legacyTables.getRowObjects() as unknown as Array<{ table_name: string }>;
    expect(legacyRows.length).toBeGreaterThan(0);

    // 新テーブルに必須カラムが存在し、データがコピーされている
    const reader = await conn.runAndReadAll(
      'SELECT id, content_digest, content_length, expires_at FROM observations WHERE id = $1',
      ['legacy_1']
    );
    const rows = reader.getRowObjects() as unknown as Array<{
      id: string;
      content_digest: string;
      content_length: number | bigint;
      expires_at: unknown;
    }>;
    expect(rows[0]?.id).toBe('legacy_1');
    expect(typeof rows[0]?.content_digest).toBe('string');
    expect(Number(rows[0]?.content_length)).toBeGreaterThan(0);
    expect(rows[0]?.expires_at).toBeDefined();

    // observeが新スキーマで動作する
    await dispatchTool('pce.memory.policy.apply', {});
    const obs = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'post-migration observation',
      extract: { mode: 'noop' },
    });
    expect(typeof obs.structuredContent?.observation_id).toBe('string');
  });
});


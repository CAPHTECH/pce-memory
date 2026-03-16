import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import { recordFeedback } from '../src/store/feedback';
import { updateCritic } from '../src/store/critic';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('feedback critic update', () => {
  it('updates critic score within bounds', async () => {
    const { claim: c } = await upsertClaim({
      text: 'foo',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'hfb',
    });
    await recordFeedback({ claim_id: c.id, signal: 'helpful', score: 1 });
    const next = await updateCritic(c.id, 1, 0, 5);
    expect(next).toBeLessThanOrEqual(5);
    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT score FROM critic WHERE claim_id = $1', [c.id]);
    const rows = reader.getRowObjects() as { score: number }[];
    expect(rows[0].score).toBe(next);
  });
});

describe('feedback active_context_id attribution', () => {
  it('stores active_context_id when provided', async () => {
    const { claim: c } = await upsertClaim({
      text: 'attribution test claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:attr-1',
    });

    const result = await recordFeedback({
      claim_id: c.id,
      signal: 'helpful',
      active_context_id: 'ac_test_123',
    });

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT active_context_id FROM feedback WHERE id = $1',
      [result.id]
    );
    const rows = reader.getRowObjects() as { active_context_id: string | null }[];
    expect(rows[0].active_context_id).toBe('ac_test_123');
  });

  it('stores NULL when active_context_id is not provided', async () => {
    const { claim: c } = await upsertClaim({
      text: 'no attribution claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:attr-2',
    });

    const result = await recordFeedback({
      claim_id: c.id,
      signal: 'harmful',
    });

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT active_context_id FROM feedback WHERE id = $1',
      [result.id]
    );
    const rows = reader.getRowObjects() as { active_context_id: string | null }[];
    expect(rows[0].active_context_id).toBeNull();
  });
});

describe('feedback migration: active_context_id column', () => {
  it('migrates legacy feedback table without active_context_id column', async () => {
    // Reset and create legacy schema (without active_context_id)
    await resetDbAsync();
    process.env.PCE_DB = ':memory:';
    await initDb();

    const conn = await getConnection();
    // Create legacy feedback table without active_context_id
    await conn.run(`
      CREATE TABLE IF NOT EXISTS feedback (
        id TEXT PRIMARY KEY,
        claim_id TEXT NOT NULL,
        signal TEXT NOT NULL,
        score DOUBLE,
        ts TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      )
    `);

    // Run initSchema (should trigger migration)
    await initSchema();

    // Verify column exists after migration
    const colReader = await conn.runAndReadAll(
      `SELECT COUNT(*)::INTEGER AS cnt FROM information_schema.columns
       WHERE table_name = 'feedback' AND column_name = 'active_context_id'`
    );
    const colRows = colReader.getRowObjects() as { cnt: number }[];
    expect(colRows[0].cnt).toBe(1);

    // Verify recordFeedback works with active_context_id
    await conn.run(`
      CREATE TABLE IF NOT EXISTS claims (
        id TEXT PRIMARY KEY, text TEXT NOT NULL, kind TEXT NOT NULL,
        scope TEXT NOT NULL, boundary_class TEXT NOT NULL,
        content_hash TEXT UNIQUE NOT NULL,
        utility REAL DEFAULT 0.0, confidence REAL DEFAULT 0.5,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        recency_anchor TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        provenance JSON
      )
    `);
    await conn.run(
      "INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash) VALUES ('clm_mig', 'test', 'fact', 'project', 'internal', 'sha256:mig')"
    );

    const result = await recordFeedback({
      claim_id: 'clm_mig',
      signal: 'helpful',
      active_context_id: 'ac_migrated',
    });

    const reader = await conn.runAndReadAll(
      'SELECT active_context_id FROM feedback WHERE id = $1',
      [result.id]
    );
    const rows = reader.getRowObjects() as { active_context_id: string | null }[];
    expect(rows[0].active_context_id).toBe('ac_migrated');
  });
});

import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
});

describe('Schema migration: claims usage tracking', () => {
  it('adds retrieval_count and last_retrieved_at to legacy claims tables', async () => {
    const conn = await getConnection();

    await conn.run(`
      CREATE TABLE claims (
        id TEXT PRIMARY KEY,
        text TEXT NOT NULL,
        kind TEXT NOT NULL,
        scope TEXT NOT NULL,
        boundary_class TEXT NOT NULL,
        memory_type TEXT,
        status TEXT DEFAULT 'active',
        content_hash TEXT UNIQUE NOT NULL,
        utility REAL DEFAULT 0.0,
        confidence REAL DEFAULT 0.5,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        recency_anchor TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        provenance JSON,
        tombstone BOOLEAN DEFAULT FALSE,
        tombstone_at TIMESTAMP,
        rollback_reason TEXT,
        superseded_by TEXT
      )
    `);
    await conn.run(
      `INSERT INTO claims (
        id, text, kind, scope, boundary_class, memory_type, status, content_hash
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8)`,
      [
        'clm_legacy',
        'legacy claim for usage migration',
        'fact',
        'project',
        'internal',
        'knowledge',
        'active',
        'sha256:legacy-usage',
      ]
    );

    await initSchema();

    const columnReader = await conn.runAndReadAll(
      `SELECT column_name
       FROM information_schema.columns
       WHERE table_name = 'claims'
         AND column_name IN ('retrieval_count', 'last_retrieved_at')
       ORDER BY column_name`
    );
    const columns = (columnReader.getRowObjects() as Array<{ column_name: string }>).map(
      (row) => row.column_name
    );
    expect(columns).toEqual(['last_retrieved_at', 'retrieval_count']);

    const rowReader = await conn.runAndReadAll(
      'SELECT retrieval_count, last_retrieved_at FROM claims WHERE id = $1',
      ['clm_legacy']
    );
    const rows = rowReader.getRowObjects() as Array<{
      retrieval_count: number | bigint | null;
      last_retrieved_at: string | null;
    }>;
    expect(Number(rows[0]?.retrieval_count ?? -1)).toBe(0);
    expect(rows[0]?.last_retrieved_at ?? null).toBeNull();
  });
});

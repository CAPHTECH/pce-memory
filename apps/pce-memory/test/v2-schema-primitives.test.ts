import { describe, it, expect, beforeEach } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { initRateState, resetRates } from '../src/store/rate';

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe('v2 schema primitives', () => {
  it('migrates legacy tables and creates new v2 primitives', async () => {
    await resetDbAsync();
    process.env.PCE_DB = ':memory:';
    await initDb();

    const conn = await getConnection();
    await conn.run(`
      CREATE TABLE IF NOT EXISTS claims (
        id TEXT PRIMARY KEY,
        text TEXT NOT NULL,
        kind TEXT NOT NULL,
        scope TEXT NOT NULL,
        boundary_class TEXT NOT NULL,
        content_hash TEXT UNIQUE NOT NULL,
        utility REAL DEFAULT 0.0,
        confidence REAL DEFAULT 0.5,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        recency_anchor TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        provenance JSON
      )
    `);
    await conn.run(`
      CREATE TABLE IF NOT EXISTS active_contexts (
        id TEXT PRIMARY KEY,
        claims JSON
      )
    `);

    await initSchema();

    const columnReader = await conn.runAndReadAll(`
      SELECT table_name, column_name
      FROM information_schema.columns
      WHERE table_name IN ('claims', 'active_contexts')
      ORDER BY table_name, column_name
    `);
    const columnRows = columnReader.getRowObjects() as Array<{
      table_name: string;
      column_name: string;
    }>;

    const columnsByTable = new Map<string, Set<string>>();
    for (const row of columnRows) {
      if (!columnsByTable.has(row.table_name)) {
        columnsByTable.set(row.table_name, new Set());
      }
      columnsByTable.get(row.table_name)!.add(row.column_name);
    }

    expect(columnsByTable.get('claims')?.has('memory_type')).toBe(true);
    expect(columnsByTable.get('claims')?.has('status')).toBe(true);
    expect(columnsByTable.get('active_contexts')?.has('intent')).toBe(true);
    expect(columnsByTable.get('active_contexts')?.has('expires_at')).toBe(true);
    expect(columnsByTable.get('active_contexts')?.has('policy_version')).toBe(true);

    const promotionColumnReader = await conn.runAndReadAll(`
      SELECT column_name
      FROM information_schema.columns
      WHERE table_name = 'promotion_queue'
      ORDER BY column_name
    `);
    const promotionColumns = new Set(
      (promotionColumnReader.getRowObjects() as Array<{ column_name: string }>).map(
        (row) => row.column_name
      )
    );
    expect(promotionColumns.has('proposed_entities')).toBe(true);
    expect(promotionColumns.has('proposed_relations')).toBe(true);

    const tableReader = await conn.runAndReadAll(`
      SELECT table_name
      FROM information_schema.tables
      WHERE table_name IN ('promotion_queue', 'active_context_items')
      ORDER BY table_name
    `);
    const tableRows = tableReader.getRowObjects() as Array<{ table_name: string }>;
    expect(tableRows.map((row) => row.table_name)).toEqual([
      'active_context_items',
      'promotion_queue',
    ]);

    await conn.run(
      `INSERT INTO promotion_queue (
        id, source_layer, target_layer, source_ids, distilled_text, candidate_hash,
        proposed_kind, proposed_scope, proposed_boundary_class, proposed_memory_type,
        provenance, evidence_ids, status, created_at
      ) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12, $13, $14)`,
      [
        'pq_test',
        'working',
        'knowledge',
        JSON.stringify(['src_1']),
        'distilled',
        'sha256:' + 'a'.repeat(64),
        'fact',
        'project',
        'internal',
        'knowledge',
        JSON.stringify({ at: '2025-01-01T00:00:00.000Z' }),
        JSON.stringify(['ev_1']),
        'pending',
        '2025-01-01T00:00:00.000Z',
      ]
    );
    await conn.run(
      `INSERT INTO active_context_items (
        id, active_context_id, claim_id, source_layer, score, rank
      ) VALUES ($1, $2, $3, $4, $5, $6)`,
      ['aci_test', 'ac_test', 'clm_test', 'knowledge', 0.9, 1]
    );

    const countsReader = await conn.runAndReadAll(`
      SELECT
        (SELECT COUNT(*)::INTEGER FROM promotion_queue) AS promotion_queue_count,
        (SELECT COUNT(*)::INTEGER FROM active_context_items) AS active_context_items_count
    `);
    const counts = countsReader.getRowObjects() as Array<{
      promotion_queue_count: number;
      active_context_items_count: number;
    }>;

    expect(counts[0]?.promotion_queue_count).toBe(1);
    expect(counts[0]?.active_context_items_count).toBe(1);

    const proposalReader = await conn.runAndReadAll(
      'SELECT proposed_entities, proposed_relations FROM promotion_queue WHERE id = $1',
      ['pq_test']
    );
    const proposalRows = proposalReader.getRowObjects() as Array<{
      proposed_entities: string;
      proposed_relations: string;
    }>;
    expect(proposalRows[0]?.proposed_entities).toBe('[]');
    expect(proposalRows[0]?.proposed_relations).toBe('[]');
  });

  it('accepts memory_type on upsert and returns it from activate', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const text = 'v2 memory type claim';
    const result = await dispatchTool('pce_memory_upsert', {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    expect(result.isError).toBeUndefined();

    const activate = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: 'v2 memory type',
      intent: 'resume_task',
    });
    const claims = activate.structuredContent?.claims as Array<{
      claim: { content_hash: string; memory_type?: string | null };
    }>;
    const activated = claims.find(
      (item) => item.claim.content_hash === `sha256:${computeContentHash(text)}`
    );

    expect(activated?.claim.memory_type).toBe('knowledge');

    const conn = await getConnection();
    const activeContextId = activate.structuredContent?.active_context_id as string;
    const reader = await conn.runAndReadAll(
      'SELECT intent, policy_version FROM active_contexts WHERE id = $1',
      [activeContextId]
    );
    const rows = reader.getRowObjects() as Array<{
      intent: string | null;
      policy_version: string | null;
    }>;

    expect(activate.structuredContent?.intent).toBe('resume_task');
    expect(rows[0]?.intent).toBe('resume_task');
    expect(rows[0]?.policy_version).toBeDefined();
  });
});

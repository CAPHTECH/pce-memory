import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';
import { gcExpiredObservations } from '../src/store/observations';

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe('pce.memory.observe', () => {
  it('TOOL_DEFINITIONSに含まれる', () => {
    const names = TOOL_DEFINITIONS.map((t) => t.name);
    expect(names).toContain('pce.memory.observe');
  });

  it('extract.mode=noop: observation_idのみ返す（claim_idsは空）', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'hello observation',
      extract: { mode: 'noop' },
    });

    expect(result.structuredContent).toBeDefined();
    const data = result.structuredContent!;
    expect(typeof data.observation_id).toBe('string');
    expect(Array.isArray(data.claim_ids)).toBe(true);
    expect(data.claim_ids).toHaveLength(0);

    // DBに保存されていること
    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT id, content FROM observations WHERE id = $1',
      [data.observation_id]
    );
    const rows = reader.getRowObjects() as unknown as { id: string; content: string | null }[];
    expect(rows[0]?.id).toBe(data.observation_id);
    expect(rows[0]?.content).toBe('hello observation');
  });

  it('extract.mode=single_claim_v0: claim_idsが返り、activate(include_meta)でEvidenceが返る', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const obs = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'my observation content',
      extract: { mode: 'single_claim_v0' },
    });
    const obsData = obs.structuredContent!;

    expect(typeof obsData.observation_id).toBe('string');
    expect(Array.isArray(obsData.claim_ids)).toBe(true);
    expect(obsData.claim_ids).toHaveLength(1);
    const claimId = (obsData.claim_ids as string[])[0]!;

    const ac = await dispatchTool('pce.memory.activate', {
      scope: ['session'],
      allow: ['answer:task'],
      include_meta: true,
    });
    const acData = ac.structuredContent!;
    expect(Array.isArray(acData.claims)).toBe(true);

    const match = (acData.claims as any[]).find((x) => x?.claim?.id === claimId);
    expect(match).toBeDefined();
    expect(Array.isArray(match.evidences)).toBe(true);

    const ev = match.evidences.find(
      (e: any) => e?.source_type === 'observation' && e?.source_id === obsData.observation_id
    );
    expect(ev).toBeDefined();
  });

  it('secret検知時: contentは保存せずextractもスキップする', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const secretText = `sk-${'A'.repeat(30)}`;
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: secretText,
      extract: { mode: 'single_claim_v0' },
    });

    const data = result.structuredContent!;
    expect(data.effective_boundary_class).toBe('secret');
    expect(data.content_stored).toBe(false);
    expect(Array.isArray(data.claim_ids)).toBe(true);
    expect(data.claim_ids).toHaveLength(0);
    expect(Array.isArray(data.warnings)).toBe(true);
    expect((data.warnings as string[])).toContain('OBS_CONTENT_NOT_STORED_SECRET');
    expect((data.warnings as string[])).toContain('EXTRACT_SKIPPED_SECRET');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string | null }[];
    expect(rows[0]?.content).toBeNull();
  });

  it('GC(scrub): 期限切れ後にcontentがNULL化される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'will be scrubbed',
      ttl_days: 1,
      extract: { mode: 'noop' },
    });
    const data = result.structuredContent!;
    const observationId = data.observation_id as string;

    // expires_atを過去にする
    const conn = await getConnection();
    await conn.run(
      "UPDATE observations SET expires_at = (CURRENT_TIMESTAMP - INTERVAL '1 day') WHERE id = $1",
      [observationId]
    );

    await gcExpiredObservations('scrub');

    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      observationId,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string | null }[];
    expect(rows[0]?.content).toBeNull();
  });
});

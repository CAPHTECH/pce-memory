import { beforeEach, describe, expect, it } from 'vitest';
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

async function applyPolicy() {
  const result = await dispatchTool('pce_memory_policy_apply', {});
  expect(result.isError).toBeUndefined();
}

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

describe('v2 design invariants', () => {
  it('raw observe cannot create durable claims', async () => {
    await applyPolicy();

    const observe = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'raw notes about retry behavior',
      })
    );

    expect(observe.claim_ids).toEqual([]);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT
         (SELECT COUNT(*)::INTEGER FROM observations) AS observation_count,
         (SELECT COUNT(*)::INTEGER FROM claims) AS claim_count,
         (SELECT COUNT(*)::INTEGER FROM claims WHERE scope IN ('project', 'principle')) AS durable_claim_count`
    );
    const rows = reader.getRowObjects() as Array<{
      observation_count: number;
      claim_count: number;
      durable_claim_count: number;
    }>;

    expect(rows[0]?.observation_count).toBe(1);
    expect(rows[0]?.claim_count).toBe(0);
    expect(rows[0]?.durable_claim_count).toBe(0);
  });

  it('provenance is required for durable promotion', async () => {
    await applyPolicy();

    const observe = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'a candidate that still needs review provenance',
        extract: { mode: 'noop' },
      })
    );
    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [observe.observation_id],
      })
    );

    const promote = await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
    });

    expect(promote.isError).toBe(true);
    expect(promote.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(promote.structuredContent?.error?.message).toContain('provenance.at');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT status FROM promotion_queue WHERE id = $1', [
      distill.candidate_id,
    ]);
    const rows = reader.getRowObjects() as Array<{ status: string }>;
    expect(rows[0]?.status).toBe('pending');
  });

  it('distill preserves boundary monotonicity', async () => {
    await applyPolicy();

    const publicObserve = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'release notes are public',
        boundary_class: 'public',
      })
    );
    const piiObserve = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'contact alice@example.com for rollout help',
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [publicObserve.observation_id, piiObserve.observation_id],
      })
    );

    expect(distill.proposed_boundary_class).toBe('pii');
    expect(
      (distill.invariant_check_results as {
        boundary_monotonicity: { max_source_boundary_class: string; passed: boolean };
      }).boundary_monotonicity
    ).toEqual(
      expect.objectContaining({
        max_source_boundary_class: 'pii',
        passed: true,
      })
    );
  });

  it('rollback is append-only', async () => {
    await applyPolicy();

    const observe = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'retry policy should back off exponentially',
      })
    );
    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [observe.observation_id],
      })
    );
    const promote = expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: { at: '2026-03-24T12:00:00.000Z', actor: 'claude' },
      })
    );

    const conn = await getConnection();
    const beforeReader = await conn.runAndReadAll(
      `SELECT
         (SELECT COUNT(*)::INTEGER FROM claims WHERE id = $1) AS claim_count,
         (SELECT COUNT(*)::INTEGER FROM promotion_queue) AS queue_count`,
      [promote.claim_id]
    );
    const beforeRows = beforeReader.getRowObjects() as Array<{
      claim_count: number;
      queue_count: number;
    }>;

    const rollback = expectSuccess(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'superseded by a safer policy',
        provenance: { at: '2026-03-24T13:00:00.000Z', actor: 'claude', note: 'invalidated' },
      })
    );

    const afterReader = await conn.runAndReadAll(
      `SELECT
         (SELECT COUNT(*)::INTEGER FROM claims WHERE id = $1) AS claim_count,
         (SELECT COUNT(*)::INTEGER FROM promotion_queue) AS queue_count`,
      [promote.claim_id]
    );
    const afterRows = afterReader.getRowObjects() as Array<{
      claim_count: number;
      queue_count: number;
    }>;

    expect(afterRows[0]?.claim_count).toBe(beforeRows[0]?.claim_count);
    expect(afterRows[0]?.queue_count).toBe((beforeRows[0]?.queue_count ?? 0) + 1);

    const rollbackReader = await conn.runAndReadAll(
      'SELECT status, accepted_claim_id, rejected_reason, provenance FROM promotion_queue WHERE id = $1',
      [rollback.rollback_id]
    );
    const rollbackRows = rollbackReader.getRowObjects() as Array<{
      status: string;
      accepted_claim_id: string;
      rejected_reason: string;
      provenance: string;
    }>;
    expect(rollbackRows[0]?.status).toBe('rolled_back');
    expect(rollbackRows[0]?.accepted_claim_id).toBe(promote.claim_id);
    expect(rollbackRows[0]?.rejected_reason).toBe('superseded by a safer policy');
    expect(
      JSON.parse(rollbackRows[0]?.provenance ?? '{}') as { rollback_of?: string }
    ).toEqual(expect.objectContaining({ rollback_of: promote.claim_id }));
  });

  it('activate persists active_context_items', async () => {
    await applyPolicy();

    expectSuccess(
      await dispatchTool('pce_memory_upsert', {
        text: 'schema review is blocking the rollout',
        kind: 'task',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'working_state',
        provenance: { at: '2026-03-24T14:00:00.000Z', actor: 'claude' },
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'schema review blocking rollout',
        intent: 'resume_task',
        top_k: 5,
      })
    );

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT source_layer, score_breakdown, selection_reason, rank
       FROM active_context_items
       WHERE active_context_id = $1
       ORDER BY rank`,
      [activate.active_context_id]
    );
    const rows = reader.getRowObjects() as Array<{
      source_layer: string | null;
      score_breakdown: string | null;
      selection_reason: string | null;
      rank: number | null;
    }>;

    expect(rows).toHaveLength(1);
    expect(rows[0]?.source_layer).toBe('meso');
    expect(rows[0]?.selection_reason).toContain('intent=resume_task');
    expect(rows[0]?.rank).toBe(1);

    const breakdown = JSON.parse(rows[0]?.score_breakdown ?? '{}') as { score_final?: number };
    expect(breakdown.score_final).toBeDefined();
  });

  it('session upsert is rejected', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'scratch work should not be durable',
      kind: 'task',
      scope: 'session',
      boundary_class: 'internal',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain("scope 'session'");
    expect(result.structuredContent?.error?.message).toContain('pce_memory_observe');
  });

  it('secret upsert is rejected', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'sk-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain("boundary_class 'secret'");
    expect(result.structuredContent?.error?.message).toContain('pce_memory_observe');
  });
});

import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { initRateState, resetRates } from '../src/store/rate';

type ActivateResponse = {
  claims: Array<{ claim: { id: string } }>;
  claims_count: number;
};

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  if (result.isError === true) {
    throw new Error(JSON.stringify(result.structuredContent ?? result.content ?? result, null, 2));
  }

  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

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

async function applyPolicy(): Promise<void> {
  expectSuccess(await dispatchTool('pce_memory_policy_apply', {}));
}

async function createClaim(input: {
  text: string;
  kind?: 'fact' | 'preference' | 'task' | 'policy_hint';
  memory_type?: 'evidence' | 'working_state' | 'knowledge' | 'procedure' | 'norm';
}): Promise<string> {
  const result = expectSuccess(
    await dispatchTool('pce_memory_upsert', {
      text: input.text,
      kind: input.kind ?? 'task',
      scope: 'project',
      boundary_class: 'internal',
      ...(input.memory_type ? { memory_type: input.memory_type } : {}),
      content_hash: `sha256:${computeContentHash(input.text)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    })
  ) as { id: string };

  return result.id;
}

async function setClaimAgeDays(claimId: string, ageDays: number): Promise<void> {
  const conn = await getConnection();
  const ts = new Date(Date.now() - ageDays * 24 * 60 * 60 * 1000).toISOString();
  await conn.run(
    'UPDATE claims SET created_at = $1, updated_at = $1, recency_anchor = $1 WHERE id = $2',
    [ts, claimId]
  );
}

async function readClaimStatus(claimId: string): Promise<string | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT status FROM claims WHERE id = $1', [claimId]);
  const rows = reader.getRowObjects() as Array<{ status: string }>;
  return rows[0]?.status;
}

async function activate(args: {
  q: string;
  include_stale_tasks?: boolean;
}): Promise<ActivateResponse> {
  return expectSuccess(
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: args.q,
      top_k: 10,
      ...(args.include_stale_tasks !== undefined
        ? { include_stale_tasks: args.include_stale_tasks }
        : {}),
    })
  ) as ActivateResponse;
}

function claimIds(response: ActivateResponse): string[] {
  return response.claims.map((item) => item.claim.id);
}

describe('working_state lifecycle', () => {
  it('activate schema exposes include_stale_tasks', () => {
    const activateTool = TOOL_DEFINITIONS.find((tool) => tool.name === 'pce_memory_activate');
    const schema = activateTool?.inputSchema?.properties?.include_stale_tasks as
      | { type?: string; default?: boolean }
      | undefined;

    expect(schema?.type).toBe('boolean');
    expect(schema?.default).toBe(false);
  });

  it('fresh working_state is active and appears in activate', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'fresh working state lifecycle task',
      memory_type: 'working_state',
    });

    const result = await activate({ q: 'fresh working state lifecycle' });

    expect(claimIds(result)).toContain(claimId);
    expect(await readClaimStatus(claimId)).toBe('active');
  });

  it('working_state older than 14 days auto-marked stale and excluded', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'stale working state lifecycle task',
      memory_type: 'working_state',
    });
    await setClaimAgeDays(claimId, 20);

    const result = await activate({ q: 'stale working state lifecycle' });

    expect(claimIds(result)).not.toContain(claimId);
    expect(result.claims_count).toBe(0);
    expect(await readClaimStatus(claimId)).toBe('stale');
  });

  it('stale working_state appears with include_stale_tasks=true', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'include stale working state lifecycle task',
      memory_type: 'working_state',
    });
    await setClaimAgeDays(claimId, 20);

    const result = await activate({
      q: 'include stale working state lifecycle',
      include_stale_tasks: true,
    });

    expect(claimIds(result)).toContain(claimId);
    expect(await readClaimStatus(claimId)).toBe('stale');
  });

  it('feedback(signal=completed) marks working_state as completed', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'completed working state lifecycle task',
      memory_type: 'working_state',
    });

    await activate({ q: 'completed working state lifecycle' });
    const feedback = expectSuccess(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claimId,
        signal: 'completed',
      })
    ) as { claim_id: string; signal: string };

    expect(feedback.claim_id).toBe(claimId);
    expect(feedback.signal).toBe('completed');
    expect(await readClaimStatus(claimId)).toBe('completed');
  });

  it('completed working_state is excluded from activate', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'exclude completed working state lifecycle task',
      memory_type: 'working_state',
    });

    await activate({ q: 'exclude completed working state lifecycle' });
    expectSuccess(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claimId,
        signal: 'completed',
      })
    );

    const result = await activate({ q: 'exclude completed working state lifecycle' });

    expect(claimIds(result)).not.toContain(claimId);
    expect(result.claims_count).toBe(0);
  });

  it('non-working_state claims are unaffected by staleness check', async () => {
    await applyPolicy();
    const claimId = await createClaim({
      text: 'old knowledge lifecycle note',
      kind: 'fact',
      memory_type: 'knowledge',
    });
    await setClaimAgeDays(claimId, 30);

    const result = await activate({ q: 'old knowledge lifecycle note' });

    expect(claimIds(result)).toContain(claimId);
    expect(await readClaimStatus(claimId)).toBe('active');
  });
});

import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetMemoryState, transitionToHasClaims } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { upsertClaim } from '../src/store/claims';
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

function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

async function seedSessionClaim(text: string, kind: 'fact' | 'task' = 'fact') {
  const result = await upsertClaim({
    text,
    kind,
    scope: 'session',
    boundary_class: 'internal',
    content_hash: `sha256:${computeContentHash(text)}`,
  });
  transitionToHasClaims(result.isNew);
  return result.claim;
}

describe('promotion pipeline', () => {
  it('registers distill/promote/rollback tools and keeps observe extraction noop-only', () => {
    const toolNames = TOOL_DEFINITIONS.map((tool) => tool.name);
    expect(toolNames).toContain('pce_memory_distill');
    expect(toolNames).toContain('pce_memory_promote');
    expect(toolNames).toContain('pce_memory_rollback');

    const observeTool = TOOL_DEFINITIONS.find((tool) => tool.name === 'pce_memory_observe');
    const extractModeSchema = (
      observeTool?.inputSchema?.properties?.extract as
        | {
            properties?: {
              mode?: { description?: string; enum?: string[] };
            };
          }
        | undefined
    )?.properties?.mode;

    expect(observeTool?.description).toContain('do not create durable claims');
    expect(extractModeSchema?.enum).toEqual(['noop']);
    expect(extractModeSchema?.description).toContain('noop preserves raw observations only');
    expect(extractModeSchema?.description).toContain('pce_memory_distill');
  });

  it('distill creates pending promotion candidates and preserves the strongest source boundary', async () => {
    await applyPolicy();

    const publicObs = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'release notes are ready',
        boundary_class: 'public',
        extract: { mode: 'noop' },
      })
    );
    const piiObs = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'customer email is alice@example.com',
        extract: { mode: 'noop' },
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [publicObs.observation_id, piiObs.observation_id],
        note: 'combine release context',
      })
    );

    expect(distill.status).toBe('pending');
    expect(distill.proposed_scope).toBe('project');
    expect(distill.proposed_kind).toBe('fact');
    expect(distill.proposed_memory_type).toBe('knowledge');
    expect(distill.proposed_boundary_class).toBe('pii');
    expect(
      (distill.invariant_check_results as { boundary_monotonicity: { max_source_boundary_class: string } })
        .boundary_monotonicity.max_source_boundary_class
    ).toBe('pii');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT status, target_layer, proposed_boundary_class, source_ids, evidence_ids, candidate_hash
       FROM promotion_queue
       WHERE id = $1`,
      [distill.candidate_id]
    );
    const rows = reader.getRowObjects() as Array<{
      status: string;
      target_layer: string;
      proposed_boundary_class: string;
      source_ids: string;
      evidence_ids: string;
      candidate_hash: string;
    }>;

    expect(rows[0]?.status).toBe('pending');
    expect(rows[0]?.target_layer).toBe('meso');
    expect(rows[0]?.proposed_boundary_class).toBe('pii');
    expect(JSON.parse(rows[0]?.source_ids ?? '[]')).toEqual(
      expect.arrayContaining([publicObs.observation_id, piiObs.observation_id])
    );
    expect(JSON.parse(rows[0]?.evidence_ids ?? '[]')).toEqual(
      expect.arrayContaining([publicObs.observation_id, piiObs.observation_id])
    );
    expect(rows[0]?.candidate_hash).toBe(`sha256:${computeContentHash(distill.distilled_text as string)}`);
  });

  it('distill accepts active_context sources and records lineage', async () => {
    await applyPolicy();

    const upsert = await seedSessionClaim('Current branch is blocked on schema review', 'task');
    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['session'],
        allow: ['answer:task'],
        q: 'blocked schema review',
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        active_context_id: activate.active_context_id,
        proposed_kind: 'task',
      })
    );

    expect(distill.proposed_kind).toBe('task');
    expect(distill.proposed_memory_type).toBe('working_state');
    expect((distill.distilled_text as string).includes('Current branch is blocked on schema review')).toBe(true);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT provenance FROM promotion_queue WHERE id = $1', [
      distill.candidate_id,
    ]);
    const rows = reader.getRowObjects() as Array<{ provenance: string }>;
    const provenance = JSON.parse(rows[0]?.provenance ?? '{}') as {
      active_context_id?: string;
      source_claim_ids?: string[];
    };

    expect(provenance.active_context_id).toBe(activate.active_context_id);
    expect(upsert.id).toBeDefined();
  });

  it('promote accepts a pending candidate, creates a durable claim, and records claim lineage evidence', async () => {
    await applyPolicy();

    const claimOne = await seedSessionClaim('We retry failed jobs with exponential backoff');
    const claimTwo = await seedSessionClaim('Retries stop after three attempts');

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_claim_ids: [claimOne.id, claimTwo.id],
        note: 'retry policy candidate',
      })
    );

    const promote = expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: { at: isoOffset(-60_000), actor: 'claude', note: 'reviewed' },
        reviewers: ['alice', 'bob'],
        review_note: 'approved for project memory',
      })
    );

    expect(promote.claim_id).toMatch(/^clm_/);
    expect(promote.is_new).toBe(true);
    expect(promote.promoted_from).toBe(distill.candidate_id);
    expect(promote.rollback_token).toBe(promote.claim_id);

    const conn = await getConnection();
    const claimReader = await conn.runAndReadAll(
      'SELECT scope, boundary_class, memory_type, provenance FROM claims WHERE id = $1',
      [promote.claim_id]
    );
    const claimRows = claimReader.getRowObjects() as Array<{
      scope: string;
      boundary_class: string;
      memory_type: string | null;
      provenance: string;
    }>;
    expect(claimRows[0]?.scope).toBe('project');
    expect(claimRows[0]?.boundary_class).toBe('internal');
    expect(claimRows[0]?.memory_type).toBe('knowledge');
    expect((JSON.parse(claimRows[0]?.provenance ?? '{}') as { note?: string }).note).toContain(
      'approved for project memory'
    );

    const queueReader = await conn.runAndReadAll(
      'SELECT status, accepted_claim_id, reviewers FROM promotion_queue WHERE id = $1',
      [distill.candidate_id]
    );
    const queueRows = queueReader.getRowObjects() as Array<{
      status: string;
      accepted_claim_id: string | null;
      reviewers: string | null;
    }>;
    expect(queueRows[0]?.status).toBe('accepted');
    expect(queueRows[0]?.accepted_claim_id).toBe(promote.claim_id);
    expect(JSON.parse(queueRows[0]?.reviewers ?? '[]')).toEqual(['alice', 'bob']);

    const evidenceReader = await conn.runAndReadAll(
      `SELECT source_type, source_id
       FROM evidence
       WHERE claim_id = $1
       ORDER BY source_type, source_id`,
      [promote.claim_id]
    );
    const evidenceRows = evidenceReader.getRowObjects() as Array<{
      source_type: string;
      source_id: string;
    }>;

    expect(evidenceRows).toEqual(
      expect.arrayContaining([
        { source_type: 'claim', source_id: claimOne.id as string },
        { source_type: 'claim', source_id: claimTwo.id as string },
      ])
    );
  });

  it('promote requires provenance', async () => {
    await applyPolicy();

    const obs = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'a pending promotion exists',
        extract: { mode: 'noop' },
      })
    );
    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
      })
    );

    const promote = await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
    });

    expect(promote.isError).toBe(true);
    expect(promote.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(promote.structuredContent?.error?.message).toContain('provenance.at');
  });

  it('promote only accepts pending candidates', async () => {
    await applyPolicy();

    const obs = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'candidate status should advance once',
        extract: { mode: 'noop' },
      })
    );
    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
      })
    );

    expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: { at: isoOffset(-50_000), actor: 'claude' },
      })
    );

    const secondPromote = await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
      provenance: { at: isoOffset(-49_000), actor: 'claude' },
    });

    expect(secondPromote.isError).toBe(true);
    expect(secondPromote.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(secondPromote.structuredContent?.error?.message).toContain('pending');
  });

  it('rollback is append-only, appends audit history, and excludes the claim from activation and redistill', async () => {
    await applyPolicy();

    const obs = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'retry policy for production incidents',
        extract: { mode: 'noop' },
      })
    );
    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
      })
    );
    const promote = expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: { at: isoOffset(-45_000), actor: 'claude' },
      })
    );

    const rollback = expectSuccess(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'superseded by a new retry design',
        provenance: { at: isoOffset(-30_000), actor: 'claude', note: 'invalidated' },
      })
    );

    expect(rollback.rollback_id).toMatch(/^rbk_/);
    expect(rollback.superseded_claim_id).toBe(promote.claim_id);

    const conn = await getConnection();
    const claimReader = await conn.runAndReadAll(
      'SELECT tombstone, rollback_reason, superseded_by FROM claims WHERE id = $1',
      [promote.claim_id]
    );
    const claimRows = claimReader.getRowObjects() as Array<{
      tombstone: boolean;
      rollback_reason: string | null;
      superseded_by: string | null;
    }>;
    expect(claimRows[0]?.tombstone).toBe(false);
    expect(claimRows[0]?.rollback_reason).toBeNull();
    expect(claimRows[0]?.superseded_by).toBeNull();

    const queueReader = await conn.runAndReadAll(
      'SELECT status, accepted_claim_id, rejected_reason FROM promotion_queue WHERE id = $1',
      [rollback.rollback_id]
    );
    const queueRows = queueReader.getRowObjects() as Array<{
      status: string;
      accepted_claim_id: string | null;
      rejected_reason: string | null;
    }>;
    expect(queueRows[0]?.status).toBe('rolled_back');
    expect(queueRows[0]?.accepted_claim_id).toBe(promote.claim_id);
    expect(queueRows[0]?.rejected_reason).toBe('superseded by a new retry design');

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'production incidents retry policy',
      })
    );
    expect(activate.claims_count).toBe(0);

    const distillRolledBackClaim = await dispatchTool('pce_memory_distill', {
      source_claim_ids: [promote.claim_id],
    });
    expect(distillRolledBackClaim.isError).toBe(true);
    expect(distillRolledBackClaim.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
  });
});

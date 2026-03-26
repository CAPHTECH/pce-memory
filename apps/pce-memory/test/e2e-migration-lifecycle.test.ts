import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import { dispatchTool, type ToolResult } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { countClaims, findClaimById } from '../src/store/claims';
import { setEmbeddingService } from '../src/store/hybridSearch';
import { initRateState, resetRates } from '../src/store/rate';
import { migrateV2MemoryType } from '../scripts/migrate-v2-memory-type.ts';

const MIGRATION_NOW = '2026-03-24T12:00:00.000Z';
const BASE_PROVENANCE_AT = '2026-03-24T08:00:00.000Z';

type SuccessResult = Record<string, unknown>;
type ErrorResult = {
  error: {
    code: string;
    message: string;
  };
};

type ClaimRecord = {
  id: string;
  kind: string;
  memory_type?: string | null;
};

type ActivateClaimResult = {
  claim: ClaimRecord;
};

type ActivateResponse = {
  active_context_id: string;
  claims: ActivateClaimResult[];
  claims_count: number;
  state: string;
};

type DistillResponse = {
  candidate_id: string;
  proposed_kind: string;
  proposed_scope: string;
  proposed_memory_type?: string | null;
  status: string;
};

type PromoteResponse = {
  claim_id: string;
  promoted_from: string;
  rollback_token: string;
  is_new: boolean;
};

type ObserveResponse = {
  observation_id: string;
  effective_boundary_class: string;
  content_stored: boolean;
  content_redacted: boolean;
  warnings?: string[];
};

type StateResponse = {
  state: string;
  policy_version: string;
  runtime_state?: {
    type: string;
    policyVersion?: string;
    claimCount?: number;
    activeContextId?: string;
  };
};

beforeEach(async () => {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  delete process.env.PCE_OBS_STORE_MODE;
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '1000';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

function hashFor(text: string): string {
  return `sha256:${computeContentHash(text)}`;
}

function provenanceAt(offsetMinutes: number): { at: string; actor: string; note: string } {
  const at = new Date(Date.parse(BASE_PROVENANCE_AT) + offsetMinutes * 60_000).toISOString();
  return {
    at,
    actor: 'vitest',
    note: `offset:${offsetMinutes}`,
  };
}

function expectSuccess<T extends SuccessResult>(result: ToolResult): T {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent as T;
}

function expectValidationError(result: ToolResult): ErrorResult {
  expect(result.isError).toBe(true);
  expect(result.structuredContent).toBeDefined();
  const error = result.structuredContent as unknown as ErrorResult;
  expect(error.error.code).toBe('VALIDATION_ERROR');
  return error;
}

async function applyPolicy(): Promise<{ state: string; policy_version: string }> {
  return expectSuccess(await dispatchTool('pce_memory_policy_apply', {})) as {
    state: string;
    policy_version: string;
  };
}

async function upsertDurableClaim(input: {
  text: string;
  kind: 'fact' | 'task' | 'preference' | 'policy_hint';
  scope: 'project' | 'principle';
  boundary_class?: 'public' | 'internal' | 'pii';
  provenance?: { at: string; actor?: string; note?: string };
  memory_type?: 'knowledge' | 'working_state' | 'procedure' | 'norm';
}): Promise<{ id: string; state: string }> {
  return expectSuccess(
    await dispatchTool('pce_memory_upsert', {
      text: input.text,
      kind: input.kind,
      scope: input.scope,
      boundary_class: input.boundary_class ?? 'internal',
      content_hash: hashFor(input.text),
      ...(input.provenance ? { provenance: input.provenance } : { provenance: provenanceAt(0) }),
      ...(input.memory_type ? { memory_type: input.memory_type } : {}),
    })
  ) as { id: string; state: string };
}

async function readState(): Promise<StateResponse> {
  return expectSuccess(await dispatchTool('pce_memory_state', { debug: true })) as StateResponse;
}

async function readObservationRow(observationId: string): Promise<{
  content: string | null;
  content_digest: string;
}> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT content, content_digest FROM observations WHERE id = $1',
    [observationId]
  );
  const rows = reader.getRowObjects() as Array<{
    content: string | null;
    content_digest: string;
  }>;
  return rows[0]!;
}

async function countPromotionQueueRows(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) AS cnt FROM promotion_queue');
  const rows = reader.getRowObjects() as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0);
}

describe('v2 migration lifecycle E2E', () => {
  it('runs the full migration flow and reports every mapped durable claim', async () => {
    await applyPolicy();

    const projectFact = await upsertDurableClaim({
      text: 'full migration flow project fact knowledge anchor',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(1),
    });
    const projectTask = await upsertDurableClaim({
      text: 'full migration flow project task working state anchor',
      kind: 'task',
      scope: 'project',
      provenance: provenanceAt(2),
    });
    const projectPreference = await upsertDurableClaim({
      text: 'full migration flow project preference procedure anchor',
      kind: 'preference',
      scope: 'project',
      provenance: provenanceAt(3),
    });
    const projectPolicyHint = await upsertDurableClaim({
      text: 'full migration flow project policy hint norm anchor',
      kind: 'policy_hint',
      scope: 'project',
      provenance: provenanceAt(4),
    });
    const principleFact = await upsertDurableClaim({
      text: 'full migration flow principle fact becomes norm anchor',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'public',
      provenance: provenanceAt(5),
    });

    const report = await migrateV2MemoryType({ now: MIGRATION_NOW });

    expect(report.run_at).toBe(MIGRATION_NOW);
    expect(report.summary).toEqual({
      total_claims_scanned: 5,
      memory_type_backfilled: 5,
      memory_type_already_set: 0,
      session_claims_scanned: 0,
      session_queue_candidates_created: 0,
      session_queue_candidates_existing: 0,
      session_claims_tombstoned: 0,
      session_claims_already_tombstoned: 0,
    });
    expect(report.mapped_counts).toEqual({
      evidence: 0,
      knowledge: 1,
      norm: 2,
      procedure: 1,
      working_state: 1,
    });
    expect(report.ambiguous_preferences).toEqual([projectPreference.id]);
    expect(report.mapped_claims).toEqual(
      expect.arrayContaining([
        { claim_id: projectFact.id, mapped_memory_type: 'knowledge' },
        { claim_id: projectTask.id, mapped_memory_type: 'working_state' },
        { claim_id: projectPreference.id, mapped_memory_type: 'procedure' },
        { claim_id: projectPolicyHint.id, mapped_memory_type: 'norm' },
        { claim_id: principleFact.id, mapped_memory_type: 'norm' },
      ])
    );

    expect((await findClaimById(projectFact.id))?.memory_type).toBe('knowledge');
    expect((await findClaimById(projectTask.id))?.memory_type).toBe('working_state');
    expect((await findClaimById(projectPreference.id))?.memory_type).toBe('procedure');
    expect((await findClaimById(projectPolicyHint.id))?.memory_type).toBe('norm');
    expect((await findClaimById(principleFact.id))?.memory_type).toBe('norm');
  });

  it('activates only migrated knowledge claims when memory_type_filter is applied after migration', async () => {
    await applyPolicy();

    const factOne = await upsertDurableClaim({
      text: 'post migration filter shared phrase migrated fact one',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(10),
    });
    const factTwo = await upsertDurableClaim({
      text: 'post migration filter shared phrase migrated fact two',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(11),
    });
    await upsertDurableClaim({
      text: 'post migration filter shared phrase migrated task',
      kind: 'task',
      scope: 'project',
      provenance: provenanceAt(12),
    });
    await upsertDurableClaim({
      text: 'post migration filter shared phrase migrated principle fact',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'public',
      provenance: provenanceAt(13),
    });

    await migrateV2MemoryType({ now: MIGRATION_NOW });

    const activate = expectSuccess<ActivateResponse>(
      await dispatchTool('pce_memory_activate', {
        scope: ['project', 'principle'],
        allow: ['answer:task'],
        q: 'post migration filter shared phrase',
        memory_type_filter: ['knowledge'],
        top_k: 10,
      })
    );
    const claims = activate.claims;
    const ids = claims.map((item) => item.claim.id).sort();

    expect(activate.state).toBe('Ready');
    expect(activate.claims_count).toBe(2);
    expect(ids).toEqual([factOne.id, factTwo.id].sort());
    expect(claims.every((item) => item.claim.kind === 'fact')).toBe(true);
    expect(claims.every((item) => item.claim.memory_type === 'knowledge')).toBe(true);
  });

  it('distills and promotes migrated knowledge into a new knowledge claim', async () => {
    await applyPolicy();

    const source = await upsertDurableClaim({
      text: 'distill after migration uses migrated knowledge claim',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(20),
    });

    await migrateV2MemoryType({ now: MIGRATION_NOW });

    const observation = expectSuccess<ObserveResponse>(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'distill after migration supporting observation',
        extract: { mode: 'noop' },
      })
    );

    const distill = expectSuccess<DistillResponse>(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [observation.observation_id],
        source_claim_ids: [source.id],
        note: 'distill migrated knowledge',
      })
    );
    expect(distill.status).toBe('pending');
    expect(distill.proposed_kind).toBe('fact');
    expect(distill.proposed_scope).toBe('project');
    expect(distill.proposed_memory_type).toBe('knowledge');

    const promote = expectSuccess<PromoteResponse>(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: provenanceAt(21),
        reviewers: ['vitest'],
        review_note: 'approved migrated knowledge',
      })
    );

    expect(promote.promoted_from).toBe(distill.candidate_id);
    expect(promote.rollback_token).toBe(promote.claim_id);
    expect(promote.is_new).toBe(true);
    expect((await findClaimById(promote.claim_id))?.memory_type).toBe('knowledge');
  });

  it('rejects session upsert after migration and points callers to observe', async () => {
    await applyPolicy();

    await upsertDurableClaim({
      text: 'session rejection setup project fact',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(30),
    });
    await migrateV2MemoryType({ now: MIGRATION_NOW });

    const error = expectValidationError(
      await dispatchTool('pce_memory_upsert', {
        text: 'session-scoped working context should be observed',
        kind: 'fact',
        scope: 'session',
        boundary_class: 'internal',
        provenance: provenanceAt(31),
      })
    );

    expect(error.error.message).toContain("scope 'session'");
    expect(error.error.message).toContain('pce_memory_observe');
  });

  it('rejects secret upserts and stores secret observations in digest-only form', async () => {
    await applyPolicy();
    process.env.PCE_OBS_STORE_MODE = 'raw';

    const secretText = `sk-${'A'.repeat(30)}`;

    const upsertError = expectValidationError(
      await dispatchTool('pce_memory_upsert', {
        text: secretText,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'secret',
        content_hash: hashFor(secretText),
        provenance: provenanceAt(40),
      })
    );
    expect(upsertError.error.message).toContain("boundary_class 'secret'");
    expect(upsertError.error.message).toContain('pce_memory_observe');

    const observe = expectSuccess<ObserveResponse>(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: secretText,
        boundary_class: 'internal',
        extract: { mode: 'noop' },
      })
    );
    const observationRow = await readObservationRow(observe.observation_id);

    expect(observe.effective_boundary_class).toBe('secret');
    expect(observe.content_stored).toBe(false);
    expect(observe.content_redacted).toBe(false);
    expect(observe.warnings).toContain('OBS_CONTENT_NOT_STORED_SECRET');
    expect(observationRow.content).toBeNull();
    expect(observationRow.content_digest).toBe('sha256:REDACTED_SECRET');
  });

  it('enforces provenance for durable upserts and accepts the same write once provenance is supplied', async () => {
    await applyPolicy();

    const missingProvenance = expectValidationError(
      await dispatchTool('pce_memory_upsert', {
        text: 'durable claim without provenance should fail',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hashFor('durable claim without provenance should fail'),
      })
    );
    expect(missingProvenance.error.message).toBe(
      'provenance.at is required for non-session scope claims'
    );

    const accepted = expectSuccess<{ id: string; state: string }>(
      await dispatchTool('pce_memory_upsert', {
        text: 'durable claim without provenance should fail',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hashFor('durable claim without provenance should fail'),
        provenance: provenanceAt(50),
      })
    );

    expect(accepted.id).toMatch(/^clm_/);
    expect(accepted.state).toBe('HasClaims');
    expect((await findClaimById(accepted.id))?.provenance?.actor).toBe('vitest');
  });

  it('tracks the full state machine lifecycle through policy_apply, upsert, activate, and feedback', async () => {
    const initial = await readState();
    expect(initial.state).toBe('Uninitialized');
    expect(initial.runtime_state?.type).toBe('Uninitialized');

    const policy = await applyPolicy();
    expect(policy.state).toBe('PolicyApplied');

    const afterPolicy = await readState();
    expect(afterPolicy.state).toBe('PolicyApplied');
    expect(afterPolicy.runtime_state?.type).toBe('PolicyApplied');

    const upsert = await upsertDurableClaim({
      text: 'state machine full cycle durable claim',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(60),
    });
    expect(upsert.state).toBe('HasClaims');

    const afterUpsert = await readState();
    expect(afterUpsert.state).toBe('HasClaims');
    expect(afterUpsert.runtime_state?.type).toBe('HasClaims');
    expect(afterUpsert.runtime_state?.claimCount).toBe(1);

    const activate = expectSuccess<ActivateResponse>(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'state machine full cycle durable claim',
        top_k: 5,
      })
    );
    expect(activate.state).toBe('Ready');
    expect(activate.active_context_id).toMatch(/^ac_/);

    const afterActivate = await readState();
    expect(afterActivate.state).toBe('Ready');
    expect(afterActivate.runtime_state?.type).toBe('Ready');
    expect(afterActivate.runtime_state?.activeContextId).toBe(activate.active_context_id);

    const feedback = expectSuccess<{ id: string; state: string }>(
      await dispatchTool('pce_memory_feedback', {
        claim_id: upsert.id,
        signal: 'helpful',
      })
    );
    expect(feedback.id).toMatch(/^fb_/);
    expect(feedback.state).toBe('Ready');

    const afterFeedback = await readState();
    expect(afterFeedback.state).toBe('Ready');
    expect(afterFeedback.runtime_state?.type).toBe('Ready');
    expect(afterFeedback.runtime_state?.activeContextId).toBe(activate.active_context_id);
  });

  it('completes concurrent upserts, activates, and distills without crashing and leaves a consistent state', async () => {
    await applyPolicy();

    const sharedSource = await upsertDurableClaim({
      text: 'concurrent lifecycle shared claim source',
      kind: 'fact',
      scope: 'project',
      provenance: provenanceAt(70),
    });
    await migrateV2MemoryType({ now: MIGRATION_NOW });

    const upserts = Array.from({ length: 10 }, (_, index) => {
      const text = `concurrent lifecycle durable claim ${index}`;
      return dispatchTool('pce_memory_upsert', {
        text,
        kind: index % 2 === 0 ? 'fact' : 'task',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: hashFor(text),
        provenance: provenanceAt(71 + index),
      });
    });

    const activates = Array.from({ length: 5 }, () =>
      dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'concurrent lifecycle',
        top_k: 20,
      })
    );

    const distills = Array.from({ length: 3 }, (_, index) =>
      dispatchTool('pce_memory_distill', {
        source_claim_ids: [sharedSource.id],
        note: `concurrent distill ${index}`,
      })
    );

    const results = await Promise.all([...upserts, ...activates, ...distills]);
    const errorResults = results
      .filter((result) => result.isError)
      .map((result) => result.structuredContent);
    for (const errorResult of errorResults) {
      const error = errorResult as ErrorResult;
      expect(['ACTIVATE_FAILED', 'DB_ERROR', 'UPSERT_FAILED', 'RATE_LIMIT', 'STATE_ERROR']).toContain(
        error.error.code
      );
    }
    expect(results.every((result) => result.structuredContent !== undefined)).toBe(true);

    const activeClaims = await countClaims();
    const queueCount = await countPromotionQueueRows();
    const finalActivate = expectSuccess<ActivateResponse>(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'concurrent lifecycle',
        top_k: 20,
      })
    );
    const state = await readState();

    expect(activeClaims).toBe(11);
    expect(queueCount).toBe(3);
    expect(finalActivate.state).toBe('Ready');
    expect(finalActivate.claims_count).toBeGreaterThan(0);
    expect(state.state).toBe('Ready');
    expect(state.runtime_state?.activeContextId).toBe(finalActivate.active_context_id);
  });
});

import { beforeEach, describe, expect, it, vi } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash } from '@pce/embeddings';

const promotionQueueFaults = {
  failNextAccept: false,
  holdPendingReads: false,
  pendingReadTarget: 2,
  pendingReadCount: 0,
  pendingReadResolvers: [] as Array<() => void>,
  reset() {
    this.failNextAccept = false;
    this.holdPendingReads = false;
    this.pendingReadCount = 0;
    this.pendingReadResolvers = [];
  },
};

vi.mock('../src/store/promotionQueue.js', async () => {
  const actual = await vi.importActual<typeof import('../src/store/promotionQueue.js')>(
    '../src/store/promotionQueue.js'
  );

  return {
    ...actual,
    async findPromotionQueueRowById(id: string) {
      const row = await actual.findPromotionQueueRowById(id);
      if (!promotionQueueFaults.holdPendingReads || !row) {
        return row;
      }

      const snapshot = { ...row };
      promotionQueueFaults.pendingReadCount += 1;
      if (promotionQueueFaults.pendingReadCount < promotionQueueFaults.pendingReadTarget) {
        await new Promise<void>((resolve) => {
          promotionQueueFaults.pendingReadResolvers.push(resolve);
        });
      } else {
        const resolvers = promotionQueueFaults.pendingReadResolvers.splice(0);
        promotionQueueFaults.pendingReadCount = 0;
        promotionQueueFaults.holdPendingReads = false;
        for (const resolve of resolvers) {
          resolve();
        }
      }

      return snapshot;
    },

    async acceptPromotionQueueRow(
      id: string,
      input: {
        accepted_claim_id: string;
        reviewers?: string | null;
        resolved_at: string;
        provenance?: string;
      }
    ) {
      if (promotionQueueFaults.failNextAccept) {
        promotionQueueFaults.failNextAccept = false;
        throw new Error('simulated db connection loss during accept');
      }
      return actual.acceptPromotionQueueRow(id, input);
    },
  };
});

import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { initRateState, resetRates } from '../src/store/rate';
import { insertObservation } from '../src/store/observations';
import { insertPromotionQueueRow, acceptPromotionQueueRow } from '../src/store/promotionQueue';
import { findClaimById, upsertClaim } from '../src/store/claims';

const STRICTNESS = {
  public: 0,
  internal: 1,
  pii: 2,
  secret: 3,
} as const;

type BoundaryClass = keyof typeof STRICTNESS;

const DURABLE_MEMORY_TYPES = ['knowledge', 'working_state', 'procedure', 'norm'] as const;

beforeEach(async () => {
  await resetSystem();
});

async function resetSystem() {
  promotionQueueFaults.reset();
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();

  delete process.env.PCE_PROMOTION_MAX_SOURCES;
  delete process.env.PCE_PROMOTION_MAX_BYTES;
  delete process.env.PCE_PROVENANCE_FUTURE_SKEW_MS;

  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';

  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();

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

async function observe(
  content: string,
  boundaryClass?: BoundaryClass
): Promise<{ observation_id: string; effective_boundary_class?: string }> {
  return expectSuccess(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      ...(boundaryClass ? { boundary_class: boundaryClass } : {}),
      extract: { mode: 'noop' },
    })
  ) as { observation_id: string; effective_boundary_class?: string };
}

async function distillFromObservations(
  observationIds: string[],
  extra: Record<string, unknown> = {}
): Promise<Record<string, unknown>> {
  return expectSuccess(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: observationIds,
      ...extra,
    })
  );
}

async function promoteCandidate(
  candidateId: string,
  overrides: Record<string, unknown> = {}
): Promise<Awaited<ReturnType<typeof dispatchTool>>> {
  return dispatchTool('pce_memory_promote', {
    candidate_id: candidateId,
    provenance: { at: isoOffset(-60_000), actor: 'claude' },
    ...overrides,
  });
}

async function rollbackClaim(
  claimId: string,
  overrides: Record<string, unknown> = {}
): Promise<Awaited<ReturnType<typeof dispatchTool>>> {
  return dispatchTool('pce_memory_rollback', {
    claim_id: claimId,
    reason: 'superseded',
    provenance: { at: isoOffset(-30_000), actor: 'claude' },
    ...overrides,
  });
}

async function createDurableClaim(text: string) {
  const obs = await observe(text);
  const distill = await distillFromObservations([obs.observation_id]);
  return expectSuccess(await promoteCandidate(distill['candidate_id'] as string)) as {
    claim_id: string;
  };
}

async function insertManualObservation(input: {
  id: string;
  content: string | null;
  boundary_class?: BoundaryClass;
  content_digest?: string;
}) {
  await insertObservation({
    id: input.id,
    source_type: 'tool',
    content: input.content,
    boundary_class: input.boundary_class ?? 'internal',
    content_digest:
      input.content_digest ??
      `sha256:${computeContentHash(typeof input.content === 'string' ? input.content : input.id)}`,
    content_length: Buffer.byteLength(input.content ?? '', 'utf8'),
    expires_at: '2026-04-24T00:00:00.000Z',
  });
}

async function readCandidateHash(candidateId: string): Promise<string | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT candidate_hash FROM promotion_queue WHERE id = $1',
    [candidateId]
  );
  const rows = reader.getRowObjects() as Array<{ candidate_hash: string }>;
  return rows[0]?.candidate_hash;
}

describe('promotion pipeline systematic boundaries', () => {
  it('rejects distill with empty sources', async () => {
    const result = await dispatchTool('pce_memory_distill', {});

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('at least one source');
  });

  it('accepts a single source and persists a deterministic candidate hash', async () => {
    const obs = await observe('single source promotion candidate');
    const distill = await distillFromObservations([obs.observation_id]);
    const candidateHash = await readCandidateHash(distill['candidate_id'] as string);

    expect(candidateHash).toBe(
      `sha256:${computeContentHash(distill['distilled_text'] as string)}`
    );
  });

  it('accepts the configured maximum number of unique sources and rejects one more', async () => {
    process.env.PCE_PROMOTION_MAX_SOURCES = '4';

    const observations = await Promise.all([
      observe('source-1'),
      observe('source-2'),
      observe('source-3'),
      observe('source-4'),
      observe('source-5'),
    ]);

    const atLimit = await dispatchTool('pce_memory_distill', {
      source_observation_ids: observations.slice(0, 4).map((item) => item.observation_id),
    });
    const aboveLimit = await dispatchTool('pce_memory_distill', {
      source_observation_ids: observations.map((item) => item.observation_id),
    });

    expect(atLimit.isError).toBeUndefined();
    expect(aboveLimit.isError).toBe(true);
    expect(aboveLimit.structuredContent?.error?.message).toContain('max 4');
  });

  it('falls back to content_digest when source observations have empty or null content', async () => {
    await insertManualObservation({
      id: 'obs_empty',
      content: '',
      content_digest: 'sha256:EMPTY_FALLBACK',
    });
    await insertManualObservation({
      id: 'obs_null',
      content: null,
      content_digest: 'sha256:NULL_FALLBACK',
    });

    const distill = await distillFromObservations(['obs_empty', 'obs_null']);
    const distilledText = distill['distilled_text'] as string;

    expect(distilledText).toContain('sha256:EMPTY_FALLBACK');
    expect(distilledText).toContain('sha256:NULL_FALLBACK');
  });

  it('rejects huge distilled text once it exceeds the configured byte limit', async () => {
    process.env.PCE_PROMOTION_MAX_BYTES = '128';
    const largeContent = 'x'.repeat(256);
    const obs = await observe(largeContent);

    const result = await dispatchTool('pce_memory_distill', {
      source_observation_ids: [obs.observation_id],
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('distilled_text too large');
  });
});

describe('promotion pipeline systematic edge cases', () => {
  it('deduplicates the same source id repeated in a distill request', async () => {
    const obs = await observe('repeatable source');
    const distill = await distillFromObservations([obs.observation_id, obs.observation_id]);
    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT source_ids FROM promotion_queue WHERE id = $1',
      [distill['candidate_id']]
    );
    const rows = reader.getRowObjects() as Array<{ source_ids: string }>;

    expect(JSON.parse(rows[0]?.source_ids ?? '[]')).toEqual([obs.observation_id]);
  });

  it('rejects promoting an already-promoted candidate and a rejected candidate', async () => {
    const obs = await observe('pending candidate');
    const candidate = await distillFromObservations([obs.observation_id]);

    expectSuccess(await promoteCandidate(candidate['candidate_id'] as string));

    const secondPromote = await promoteCandidate(candidate['candidate_id'] as string, {
      provenance: { at: isoOffset(-50_000), actor: 'claude' },
    });
    expect(secondPromote.isError).toBe(true);
    expect(secondPromote.structuredContent?.error?.message).toContain('pending');

    await insertPromotionQueueRow({
      id: 'pq_rejected',
      source_layer: 'micro',
      target_layer: 'meso',
      source_ids: JSON.stringify(['obs_rejected']),
      distilled_text: 'rejected candidate',
      candidate_hash: `sha256:${computeContentHash('rejected candidate')}`,
      proposed_kind: 'fact',
      proposed_scope: 'project',
      proposed_boundary_class: 'internal',
      provenance: JSON.stringify({ source_observation_ids: ['obs_rejected'] }),
      evidence_ids: JSON.stringify([]),
      status: 'rejected',
      created_at: isoOffset(-120_000),
      rejected_reason: 'manual rejection',
    });

    const rejectedPromote = await promoteCandidate('pq_rejected');
    expect(rejectedPromote.isError).toBe(true);
    expect(rejectedPromote.structuredContent?.error?.message).toContain('pending');
  });

  it('rejects rollback for missing and already rolled-back claims', async () => {
    const missing = await rollbackClaim('clm_missing');
    expect(missing.isError).toBe(true);
    expect(missing.structuredContent?.error?.message).toContain('claim not found');

    const promoted = await createDurableClaim('claim to rollback once');
    expectSuccess(await rollbackClaim(promoted.claim_id));

    const secondRollback = await rollbackClaim(promoted.claim_id, {
      provenance: { at: isoOffset(-20_000), actor: 'claude' },
    });
    expect(secondRollback.isError).toBe(true);
    expect(secondRollback.structuredContent?.error?.message).toContain('already rolled back');
  });

  it('rejects distill from a rolled-back claim', async () => {
    const promoted = await createDurableClaim('rolled back source');
    expectSuccess(await rollbackClaim(promoted.claim_id));

    const result = await dispatchTool('pce_memory_distill', {
      source_claim_ids: [promoted.claim_id],
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.message).toContain('claim sources were not found');
  });

  it('allows distill and promote to proceed concurrently without corrupting queue state', async () => {
    const obs = await observe('concurrent distill and promote');
    const initialCandidate = await distillFromObservations([obs.observation_id]);

    const [promote, distill] = await Promise.all([
      promoteCandidate(initialCandidate['candidate_id'] as string),
      dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_kind: 'fact',
      }),
    ]);

    expect(promote.isError).toBeUndefined();
    expect(distill.isError).toBeUndefined();

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT status, COUNT(*)::INTEGER AS cnt
       FROM promotion_queue
       GROUP BY status
       ORDER BY status`
    );
    const rows = reader.getRowObjects() as Array<{ status: string; cnt: number }>;

    expect(rows).toEqual(
      expect.arrayContaining([
        { status: 'accepted', cnt: 1 },
        { status: 'pending', cnt: 1 },
      ])
    );
  });
});

describe('promotion pipeline systematic failures', () => {
  it('rejects invalid candidate kind/scope/boundary values', async () => {
    const base = {
      source_layer: 'micro',
      target_layer: 'meso',
      source_ids: JSON.stringify(['obs_invalid']),
      distilled_text: 'invalid candidate',
      candidate_hash: `sha256:${computeContentHash('invalid candidate')}`,
      provenance: JSON.stringify({ source_observation_ids: ['obs_invalid'] }),
      evidence_ids: JSON.stringify([]),
      status: 'pending',
      created_at: isoOffset(-120_000),
    };

    const cases = [
      {
        id: 'pq_invalid_kind',
        row: { ...base, proposed_kind: 'bogus', proposed_scope: 'project', proposed_boundary_class: 'internal' },
        message: 'proposed_kind',
      },
      {
        id: 'pq_invalid_scope',
        row: { ...base, proposed_kind: 'fact', proposed_scope: 'session', proposed_boundary_class: 'internal' },
        message: 'proposed_scope',
      },
      {
        id: 'pq_invalid_boundary',
        row: { ...base, proposed_kind: 'fact', proposed_scope: 'project', proposed_boundary_class: 'ultra_secret' },
        message: 'proposed_boundary_class',
      },
    ];

    for (const testCase of cases) {
      await insertPromotionQueueRow({
        id: testCase.id,
        ...testCase.row,
      });

      const result = await promoteCandidate(testCase.id);
      expect(result.isError).toBe(true);
      expect(result.structuredContent?.error?.message).toContain(testCase.message);
    }
  });

  it('rejects future provenance for promote and rollback', async () => {
    process.env.PCE_PROVENANCE_FUTURE_SKEW_MS = '0';

    const obs = await observe('future provenance candidate');
    const candidate = await distillFromObservations([obs.observation_id]);

    const futurePromote = await promoteCandidate(candidate['candidate_id'] as string, {
      provenance: { at: '2099-01-01T00:00:00.000Z', actor: 'claude' },
    });
    expect(futurePromote.isError).toBe(true);
    expect(futurePromote.structuredContent?.error?.message).toContain('future');

    const durableClaim = await createDurableClaim('rollback future provenance');
    const futureRollback = await rollbackClaim(durableClaim.claim_id, {
      provenance: { at: '2099-01-01T00:00:00.000Z', actor: 'claude' },
    });
    expect(futureRollback.isError).toBe(true);
    expect(futureRollback.structuredContent?.error?.message).toContain('future');
  });

  it('rejects candidate_hash collisions when the existing claim metadata does not match', async () => {
    const obs = await observe('same text, different metadata');
    const factCandidate = await distillFromObservations([obs.observation_id], {
      proposed_kind: 'fact',
      proposed_scope: 'project',
    });
    const taskCandidate = await distillFromObservations([obs.observation_id], {
      proposed_kind: 'task',
      proposed_scope: 'project',
    });

    expectSuccess(await promoteCandidate(factCandidate['candidate_id'] as string));

    const collision = await promoteCandidate(taskCandidate['candidate_id'] as string, {
      provenance: { at: isoOffset(-45_000), actor: 'claude' },
    });

    expect(collision.isError).toBe(true);
    expect(collision.structuredContent?.error?.message).toContain('candidate_hash collides');
  });

  it('rolls back promote when the DB fails during accept', async () => {
    const obs = await observe('fault injection candidate');
    const candidate = await distillFromObservations([obs.observation_id]);

    promotionQueueFaults.failNextAccept = true;
    const result = await promoteCandidate(candidate['candidate_id'] as string);

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.message).toContain('simulated db connection loss');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT
         (SELECT COUNT(*)::INTEGER FROM claims WHERE scope IN ('project', 'principle')) AS durable_claim_count,
         (SELECT status FROM promotion_queue WHERE id = $1) AS status`,
      [candidate['candidate_id']]
    );
    const rows = reader.getRowObjects() as Array<{
      durable_claim_count: number;
      status: string;
    }>;

    expect(rows[0]?.durable_claim_count).toBe(0);
    expect(rows[0]?.status).toBe('pending');
  });

  it('allows only one concurrent promote transition for the same candidate', async () => {
    const obs = await observe('race on single candidate');
    const candidate = await distillFromObservations([obs.observation_id]);

    const [first, second] = await Promise.all([
      promoteCandidate(candidate['candidate_id'] as string, {
        provenance: { at: isoOffset(-40_000), actor: 'claude' },
      }),
      promoteCandidate(candidate['candidate_id'] as string, {
        provenance: { at: isoOffset(-39_000), actor: 'claude' },
      }),
    ]);

    const successes = [first, second].filter((result) => !result.isError);
    const failures = [first, second].filter((result) => result.isError);

    expect(successes).toHaveLength(1);
    expect(failures).toHaveLength(1);
    expect(failures[0]?.structuredContent?.error?.message).toContain('pending');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      `SELECT
         (SELECT COUNT(*)::INTEGER FROM claims WHERE scope IN ('project', 'principle')) AS durable_claim_count,
         (SELECT status FROM promotion_queue WHERE id = $1) AS status`,
      [candidate['candidate_id']]
    );
    const rows = reader.getRowObjects() as Array<{
      durable_claim_count: number;
      status: string;
    }>;

    expect(rows[0]?.durable_claim_count).toBe(1);
    expect(rows[0]?.status).toBe('accepted');
  });
});

describe('Property: promotion pipeline', () => {
  it('Property: candidate_hash is deterministic for the same ordered sources', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(fc.uuid().map((id) => `note-${id}`), { minLength: 1, maxLength: 4 }),
        async (texts) => {
          await resetSystem();

          const observationIds: string[] = [];
          for (const text of texts) {
            const obs = await observe(text);
            observationIds.push(obs.observation_id);
          }

          const first = await distillFromObservations(observationIds);
          const second = await distillFromObservations(observationIds);
          const firstHash = await readCandidateHash(first['candidate_id'] as string);
          const secondHash = await readCandidateHash(second['candidate_id'] as string);

          expect(firstHash).toBe(secondHash);
          expect(firstHash).toBe(
            `sha256:${computeContentHash(first['distilled_text'] as string)}`
          );
        }
      ),
      { numRuns: 10 }
    );
  });

  it('Property: boundary monotonicity always holds', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(fc.constantFrom<BoundaryClass>('public', 'internal', 'pii', 'secret'), {
          minLength: 1,
          maxLength: 4,
        }),
        async (boundaries) => {
          await resetSystem();

          const observationIds: string[] = [];
          for (const [index, boundary] of boundaries.entries()) {
            const obs = await observe(`boundary-${index}`, boundary);
            observationIds.push(obs.observation_id);
          }

          const distill = await distillFromObservations(observationIds);
          const expectedBoundary = boundaries.reduce((current, candidate) =>
            STRICTNESS[candidate] > STRICTNESS[current] ? candidate : current
          );

          expect(distill['proposed_boundary_class']).toBe(expectedBoundary);
        }
      ),
      { numRuns: 10 }
    );
  });

  it('Property: promotion queue status transitions follow the pending -> accepted FSM', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.constantFrom('pending', 'accepted', 'rejected', 'rolled_back'),
        fc.integer({ min: 1, max: 3 }),
        async (initialStatus, attempts) => {
          await resetSystem();

          await insertPromotionQueueRow({
            id: 'pq_fsm',
            source_layer: 'micro',
            target_layer: 'meso',
            source_ids: JSON.stringify(['obs_fsm']),
            distilled_text: 'fsm candidate',
            candidate_hash: `sha256:${computeContentHash('fsm candidate')}`,
            proposed_kind: 'fact',
            proposed_scope: 'project',
            proposed_boundary_class: 'internal',
            provenance: JSON.stringify({ source_observation_ids: ['obs_fsm'] }),
            evidence_ids: JSON.stringify([]),
            status: initialStatus,
            created_at: isoOffset(-120_000),
            ...(initialStatus === 'accepted' ? { accepted_claim_id: 'clm_existing' } : {}),
          });

          const outcomes: boolean[] = [];
          for (let index = 0; index < attempts; index += 1) {
            outcomes.push(
              await acceptPromotionQueueRow('pq_fsm', {
                accepted_claim_id: `clm_${index}`,
                resolved_at: isoOffset(-20_000 + index * 1_000),
              })
            );
          }

          const conn = await getConnection();
          const reader = await conn.runAndReadAll(
            'SELECT status FROM promotion_queue WHERE id = $1',
            ['pq_fsm']
          );
          const rows = reader.getRowObjects() as Array<{ status: string }>;
          const expectedFinalStatus = initialStatus === 'pending' ? 'accepted' : initialStatus;

          expect(rows[0]?.status).toBe(expectedFinalStatus);
          expect(outcomes.filter(Boolean)).toHaveLength(initialStatus === 'pending' ? 1 : 0);
        }
      ),
      { numRuns: 12 }
    );
  });

  it('Property: rollback never mutates original claim data', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uuid().map((id) => `claim-${id}`),
        fc.constantFrom('fact', 'preference', 'task', 'policy_hint'),
        fc.constantFrom('project', 'principle'),
        fc.constantFrom('public', 'internal', 'pii'),
        fc.option(fc.constantFrom(...DURABLE_MEMORY_TYPES), { nil: undefined }),
        async (text, kind, scope, boundaryClass, memoryType) => {
          await resetSystem();

          const inserted = await upsertClaim({
            text,
            kind,
            scope,
            boundary_class: boundaryClass,
            ...(memoryType ? { memory_type: memoryType } : {}),
            content_hash: `sha256:${computeContentHash(text)}`,
            provenance: { at: isoOffset(-60_000), actor: 'claude' },
          });

          const before = await findClaimById(inserted.claim.id);
          expect(before).toBeDefined();

          const rollback = await rollbackClaim(inserted.claim.id, {
            provenance: { at: isoOffset(-30_000), actor: 'claude' },
          });
          expect(rollback.isError).toBeUndefined();

          const after = await findClaimById(inserted.claim.id);
          expect(after).toBeDefined();
          expect(after?.text).toBe(before?.text);
          expect(after?.kind).toBe(before?.kind);
          expect(after?.scope).toBe(before?.scope);
          expect(after?.boundary_class).toBe(before?.boundary_class);
          expect(after?.memory_type ?? null).toBe(before?.memory_type ?? null);
          expect(after?.content_hash).toBe(before?.content_hash);
          expect(after?.provenance).toEqual(before?.provenance);
        }
      ),
      { numRuns: 10 }
    );
  });
});

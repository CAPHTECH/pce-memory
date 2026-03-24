import { beforeEach, describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { CLAIM_KINDS, type ClaimKind } from '../src/domain/types';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { getStateType, resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';

type ValidUpsertInput = {
  text: string;
  kind: ClaimKind;
  scope: 'project' | 'principle';
  boundary_class: 'public' | 'internal' | 'pii';
  memory_type: 'knowledge' | 'working_state' | 'procedure' | 'norm';
  provenance: { at: string; actor: string };
};

const BOUNDARY_STRICTNESS = {
  public: 0,
  internal: 1,
  pii: 2,
  secret: 3,
} as const;

async function setupRuntime() {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  delete process.env.PCE_OBS_MAX_BYTES;
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

beforeEach(async () => {
  await setupRuntime();
});

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

function expectError(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBe(true);
  expect(result.structuredContent?.error?.code).toEqual(expect.any(String));
  expect(result.structuredContent?.error?.message).toEqual(expect.any(String));
  return result.structuredContent?.error as { code: string; message: string };
}

async function applyPolicy() {
  expectSuccess(await dispatchTool('pce_memory_policy_apply', {}));
}

const safeTextArb = fc
  .array(fc.constantFrom(...'abcdefghijklmnopqrstuvwxyz0123456789 '.split('')), {
    minLength: 1,
    maxLength: 40,
  })
  .map((chars) => chars.join('').trim())
  .filter((value) => value.length > 0);

const validUpsertInputArb: fc.Arbitrary<ValidUpsertInput> = fc
  .record({
    text: safeTextArb,
    kind: fc.constantFrom<ClaimKind>(...CLAIM_KINDS),
    boundary_class: fc.constantFrom<'public' | 'internal' | 'pii'>('public', 'internal', 'pii'),
  })
  .map(({ text, kind, boundary_class }) => ({
    text: `${text}-${crypto.randomUUID().slice(0, 8)}`,
    kind,
    scope: kind === 'policy_hint' ? 'principle' : 'project',
    boundary_class,
    memory_type:
      kind === 'task'
        ? 'working_state'
        : kind === 'policy_hint'
          ? 'norm'
          : kind === 'preference'
            ? 'procedure'
            : 'knowledge',
    provenance: { at: '2026-03-24T12:00:00.000Z', actor: 'claude' },
  }));

const nonSecretBoundaryArb = fc.constantFrom<'public' | 'internal' | 'pii'>(
  'public',
  'internal',
  'pii'
);

describe('Property: handler validation and state invariants', () => {
  it('Property: any valid upsert input is retrievable via activate', async () => {
    await applyPolicy();

    await fc.assert(
      fc.asyncProperty(validUpsertInputArb, async (input) => {
        const upsert = expectSuccess(await dispatchTool('pce_memory_upsert', input));
        const activate = expectSuccess(
          await dispatchTool('pce_memory_activate', {
            scope: [input.scope],
            allow: ['answer:task', 'tool:contact-lookup'],
            q: input.text,
            top_k: 20,
          })
        );

        const claims = activate.claims as Array<{ claim: { id: string; text: string } }>;
        expect(claims).toEqual(
          expect.arrayContaining([
            expect.objectContaining({
              claim: expect.objectContaining({
                id: upsert.id,
                text: input.text,
              }),
            }),
          ])
        );
      }),
      { numRuns: 20 }
    );
  });

  it('Property: boundary monotonicity holds through distill plus promote', async () => {
    await applyPolicy();

    await fc.assert(
      fc.asyncProperty(fc.array(nonSecretBoundaryArb, { minLength: 1, maxLength: 3 }), async (boundaries) => {
        const observationIds: string[] = [];

        for (const boundary of boundaries) {
          const content = `${boundary} review note alpha bravo charlie ${String.fromCharCode(
            97 + observationIds.length
          )}`;
          const observe = expectSuccess(
            await dispatchTool('pce_memory_observe', {
              source_type: 'chat',
              content,
              boundary_class: boundary,
              extract: { mode: 'noop' },
            })
          );
          observationIds.push(observe.observation_id as string);
        }

        const distill = expectSuccess(
          await dispatchTool('pce_memory_distill', {
            source_observation_ids: observationIds,
            note: 'property-based monotonicity check',
          })
        );

        const expectedBoundary = boundaries.reduce((current, candidate) =>
          BOUNDARY_STRICTNESS[candidate] > BOUNDARY_STRICTNESS[current] ? candidate : current
        );

        expect(distill.proposed_boundary_class).toBe(expectedBoundary);

        const promote = expectSuccess(
          await dispatchTool('pce_memory_promote', {
            candidate_id: distill.candidate_id,
            provenance: { at: '2026-03-24T13:00:00.000Z', actor: 'claude' },
          })
        );

        const conn = await getConnection();
        const reader = await conn.runAndReadAll(
          'SELECT boundary_class FROM claims WHERE id = $1',
          [promote.claim_id]
        );
        const rows = reader.getRowObjects() as Array<{ boundary_class: 'public' | 'internal' | 'pii' }>;
        expect(rows[0]?.boundary_class).toBe(expectedBoundary);
      }),
      { numRuns: 15 }
    );
  });

  it('Property: every error response has error.code and error.message', async () => {
    await applyPolicy();

    await fc.assert(
      fc.asyncProperty(
        fc.constantFrom(
          {
            name: 'pce_memory_upsert',
            args: {
              text: 'invalid-kind',
              kind: 'incident',
              scope: 'project',
              boundary_class: 'internal',
              provenance: { at: '2026-03-24T12:00:00.000Z' },
            },
          },
          {
            name: 'pce_memory_observe',
            args: {
              source_type: 'chat',
              content: '',
              extract: { mode: 'noop' },
            },
          },
          {
            name: 'pce_memory_distill',
            args: {},
          },
          {
            name: 'pce_memory_promote',
            args: {
              candidate_id: '',
              provenance: { at: '2026-03-24T12:00:00.000Z' },
            },
          },
          {
            name: 'pce_memory_rollback',
            args: {
              claim_id: '',
              reason: '',
              provenance: { at: '2026-03-24T12:00:00.000Z' },
            },
          }
        ),
        async (invalidCall) => {
          const error = expectError(
            await dispatchTool(
              invalidCall.name,
              invalidCall.args as Record<string, unknown>
            )
          );
          expect(error.code.length).toBeGreaterThan(0);
          expect(error.message.length).toBeGreaterThan(0);
        }
      ),
      { numRuns: 30 }
    );
  });

  it('Property: state machine transitions follow Uninitialized to PolicyApplied to HasClaims to Ready', async () => {
    await fc.assert(
      fc.asyncProperty(validUpsertInputArb, async (input) => {
        await setupRuntime();
        expect(getStateType()).toBe('Uninitialized');

        expectSuccess(await dispatchTool('pce_memory_policy_apply', {}));
        expect(getStateType()).toBe('PolicyApplied');

        expectSuccess(await dispatchTool('pce_memory_upsert', input));
        expect(getStateType()).toBe('HasClaims');

        expectSuccess(
          await dispatchTool('pce_memory_activate', {
            scope: [input.scope],
            allow: ['answer:task', 'tool:contact-lookup'],
            q: input.text,
            top_k: 10,
          })
        );
        expect(getStateType()).toBe('Ready');
      }),
      { numRuns: 12 }
    );
  });
});

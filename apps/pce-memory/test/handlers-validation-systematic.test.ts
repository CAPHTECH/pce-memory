import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { MEMORY_TYPES } from '../src/domain/types';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';

function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

function validProvenance(msOffset: number = -60_000) {
  return { at: isoOffset(msOffset), actor: 'claude' };
}

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
  expect(result.isError ?? false).toBe(false);
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

function expectError(
  result: Awaited<ReturnType<typeof dispatchTool>>,
  expectedCode: string = 'VALIDATION_ERROR'
) {
  expect(result.isError).toBe(true);
  expect(result.structuredContent?.error?.code).toBe(expectedCode);
  expect(result.structuredContent?.error?.message).toEqual(expect.any(String));
  return result.structuredContent?.error as { code: string; message: string };
}

async function applyPolicy() {
  const result = await dispatchTool('pce_memory_policy_apply', {});
  expectSuccess(result);
}

async function countClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*)::INTEGER AS count FROM claims');
  const rows = reader.getRowObjects() as Array<{ count: number }>;
  return rows[0]?.count ?? 0;
}

async function createPendingCandidate(boundaryClass: 'public' | 'internal' | 'pii' = 'internal') {
  const observation = expectSuccess(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content: `candidate-${boundaryClass}-${crypto.randomUUID()}`,
      boundary_class: boundaryClass,
      extract: { mode: 'noop' },
    })
  );

  return expectSuccess(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: [observation.observation_id],
      note: 'systematic validation candidate',
    })
  );
}

async function createPromotedClaim() {
  const candidate = await createPendingCandidate('internal');
  const promote = expectSuccess(
    await dispatchTool('pce_memory_promote', {
      candidate_id: candidate.candidate_id,
      provenance: validProvenance(),
      review_note: 'approved for rollback validation',
    })
  );
  return { candidate, promote };
}

describe('systematic boundary validation', () => {
  describe('upsert rejects invalid boundary_class inputs', () => {
    const invalidBoundaryClasses: Array<{ label: string; value: unknown }> = [
      { label: 'empty string', value: '' },
      { label: 'wrong case', value: 'PUBLIC' },
      { label: 'unknown enum', value: 'confidential' },
      { label: 'whitespace suffix', value: 'internal ' },
      { label: 'number', value: 42 },
      { label: 'array', value: ['internal'] },
      { label: 'object', value: { boundary_class: 'internal' } },
      { label: 'null', value: null },
    ];

    for (const invalidBoundaryClass of invalidBoundaryClasses) {
      it(`rejects ${invalidBoundaryClass.label}`, async () => {
        await applyPolicy();

        const result = await dispatchTool('pce_memory_upsert', {
          text: `invalid-boundary-${invalidBoundaryClass.label}`,
          kind: 'fact',
          scope: 'project',
          boundary_class: invalidBoundaryClass.value,
          provenance: validProvenance(),
        });

        expectError(result);
        expect(await countClaims()).toBe(0);
      });
    }

    it('rejects secret boundary_class for durable upsert', async () => {
      await applyPolicy();

      const result = await dispatchTool('pce_memory_upsert', {
        text: 'secret claim should not be durable',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'secret',
        provenance: validProvenance(),
      });

      const error = expectError(result);
      expect(error.message).toContain("boundary_class 'secret'");
      expect(await countClaims()).toBe(0);
    });
  });

  describe('upsert rejects invalid kind inputs', () => {
    const invalidKinds: Array<{ label: string; value: unknown }> = [
      { label: 'empty string', value: '' },
      { label: 'wrong case', value: 'FACT' },
      { label: 'unknown enum', value: 'incident' },
      { label: 'trailing whitespace', value: 'task ' },
      { label: 'number', value: 7 },
      { label: 'null', value: null },
      { label: 'object', value: { kind: 'fact' } },
    ];

    for (const invalidKind of invalidKinds) {
      it(`rejects ${invalidKind.label}`, async () => {
        await applyPolicy();

        const result = await dispatchTool('pce_memory_upsert', {
          text: `invalid-kind-${invalidKind.label}`,
          kind: invalidKind.value,
          scope: 'project',
          boundary_class: 'internal',
          provenance: validProvenance(),
        });

        expectError(result);
        expect(await countClaims()).toBe(0);
      });
    }
  });

  describe('upsert rejects invalid scope inputs', () => {
    const invalidScopes: Array<{ label: string; value: unknown }> = [
      { label: 'empty string', value: '' },
      { label: 'unknown enum', value: 'global' },
      { label: 'wrong case', value: 'PROJECT' },
      { label: 'whitespace suffix', value: 'principle ' },
      { label: 'number', value: 1 },
      { label: 'null', value: null },
      { label: 'object', value: { scope: 'project' } },
    ];

    for (const invalidScope of invalidScopes) {
      it(`rejects ${invalidScope.label}`, async () => {
        await applyPolicy();

        const result = await dispatchTool('pce_memory_upsert', {
          text: `invalid-scope-${invalidScope.label}`,
          kind: 'fact',
          scope: invalidScope.value,
          boundary_class: 'internal',
          provenance: validProvenance(),
        });

        expectError(result);
        expect(await countClaims()).toBe(0);
      });
    }

    it('rejects session scope for durable upsert', async () => {
      await applyPolicy();

      const result = await dispatchTool('pce_memory_upsert', {
        text: 'session scope should be observed, not upserted',
        kind: 'task',
        scope: 'session',
        boundary_class: 'internal',
        provenance: validProvenance(),
      });

      const error = expectError(result);
      expect(error.message).toContain("scope 'session'");
      expect(error.message).toContain('pce_memory_observe');
    });
  });

  it('observe rejects empty content', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content: '',
      extract: { mode: 'noop' },
    });

    const error = expectError(result);
    expect(error.message).toBe('content is required');
  });

  it('observe rejects content exceeding the configured byte limit', async () => {
    await applyPolicy();
    process.env.PCE_OBS_MAX_BYTES = '16';

    const result = await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content: 'x'.repeat(17),
      extract: { mode: 'noop' },
    });

    const error = expectError(result);
    expect(error.message).toBe('content too large');
  });

  it('distill rejects requests with zero sources', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_distill', {});

    const error = expectError(result);
    expect(error.message).toBe('at least one source is required');
  });

  it('distill preserves the strongest boundary across mixed non-secret classes', async () => {
    await applyPolicy();

    const publicObservation = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'public release note',
        boundary_class: 'public',
        extract: { mode: 'noop' },
      })
    );
    const piiObservation = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'contact alice@example.com',
        boundary_class: 'pii',
        extract: { mode: 'noop' },
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [publicObservation.observation_id, piiObservation.observation_id],
      })
    );

    expect(distill.proposed_boundary_class).toBe('pii');
    expect(
      (
        distill.invariant_check_results as {
          boundary_monotonicity: { max_source_boundary_class: string; passed: boolean };
        }
      ).boundary_monotonicity
    ).toEqual(
      expect.objectContaining({
        max_source_boundary_class: 'pii',
        passed: true,
      })
    );
  });

  it('distill escalates mixed public and secret sources to secret', async () => {
    await applyPolicy();

    const publicObservation = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'public rollout plan',
        boundary_class: 'public',
        extract: { mode: 'noop' },
      })
    );
    const secretObservation = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'sk-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
        boundary_class: 'internal',
        extract: { mode: 'noop' },
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [publicObservation.observation_id, secretObservation.observation_id],
      })
    );

    expect(distill.proposed_boundary_class).toBe('secret');
  });
});

describe('systematic edge-case validation', () => {
  it('rejects invalid provenance.at on upsert', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'invalid provenance format',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: { at: '2026/03/24 12:00:00' },
    });

    const error = expectError(result);
    expect(error.message).toContain('valid ISO8601 datetime with timezone');
  });

  it('rejects invalid provenance.at on observe when provenance is supplied', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content: 'observe invalid provenance',
      provenance: { at: 'not-a-date' },
      extract: { mode: 'noop' },
    });

    const error = expectError(result);
    expect(error.message).toContain('valid ISO8601 datetime with timezone');
  });

  it('rejects invalid provenance.at on promote', async () => {
    await applyPolicy();
    const candidate = await createPendingCandidate();

    const result = await dispatchTool('pce_memory_promote', {
      candidate_id: candidate.candidate_id,
      provenance: { at: '2026-13-01T00:00:00Z' },
    });

    const error = expectError(result);
    expect(error.message).toContain('valid ISO8601 datetime with timezone');
  });

  it('rejects invalid provenance.at on rollback', async () => {
    await applyPolicy();
    const { promote } = await createPromotedClaim();

    const result = await dispatchTool('pce_memory_rollback', {
      claim_id: promote.claim_id,
      reason: 'invalid rollback timestamp',
      provenance: { at: '2026-03-24T25:00:00Z' },
    });

    const error = expectError(result);
    expect(error.message).toContain('valid ISO8601 datetime with timezone');
  });

  it('accepts provenance.at timezone edge offsets', async () => {
    await applyPolicy();

    const first = await dispatchTool('pce_memory_upsert', {
      text: 'timezone edge plus fourteen',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: { at: '2025-03-24T23:59:59+14:00', actor: 'claude' },
    });
    const second = await dispatchTool('pce_memory_upsert', {
      text: 'timezone edge minus twelve',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: { at: '2025-03-24T00:00:00-12:00', actor: 'claude' },
    });

    expectSuccess(first);
    expectSuccess(second);
    expect(await countClaims()).toBe(2);
  });

  it('rejects content_hash mismatch and leaves the claim table untouched', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'content hash mismatch target',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '0'.repeat(64),
      provenance: validProvenance(),
    });

    const error = expectError(result);
    expect(error.message).toContain('content_hash mismatch');
    expect(await countClaims()).toBe(0);
  });

  it('rejects extra unknown fields on upsert', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'unknown field should fail',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: validProvenance(),
      unexpected: 'field',
    });

    const error = expectError(result);
    expect(error.message).toContain('unknown fields: unexpected');
  });

  it('rejects memory_type values outside the MemoryType enum', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'invalid memory type',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'archive',
      provenance: validProvenance(),
    });

    const error = expectError(result);
    expect(error.message).toBe('unknown memory_type');
  });

  it('continues to accept valid MemoryType values used by activate', async () => {
    await applyPolicy();

    for (const memoryType of MEMORY_TYPES) {
      const result = await dispatchTool('pce_memory_upsert', {
        text: `memory-type-${memoryType}-${crypto.randomUUID()}`,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: memoryType,
        provenance: validProvenance(),
      });

      expectSuccess(result);
    }
  });
});

describe('systematic security regression coverage', () => {
  it('stores SQL injection payloads in text as inert data', async () => {
    await applyPolicy();
    const payload = "fact'); DROP TABLE claims; --";
    const contentHash = `sha256:${computeContentHash(payload)}`;

    const upsert = expectSuccess(
      await dispatchTool('pce_memory_upsert', {
        text: payload,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: contentHash,
        provenance: validProvenance(),
      })
    );

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT text FROM claims WHERE id = $1', [upsert.id]);
    const rows = reader.getRowObjects() as Array<{ text: string }>;
    expect(rows[0]?.text).toBe(payload);
    expect(await countClaims()).toBe(1);
  });

  it('rejects SQL injection payloads in kind and keeps the schema intact', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'sql-injection-kind',
      kind: "fact'); DROP TABLE claims; --",
      scope: 'project',
      boundary_class: 'internal',
      provenance: validProvenance(),
    });

    expectError(result);
    expect(await countClaims()).toBe(0);
  });

  it('rejects SQL injection payloads in scope and keeps the schema intact', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'sql-injection-scope',
      kind: 'fact',
      scope: "project'); DROP TABLE claims; --",
      boundary_class: 'internal',
      provenance: validProvenance(),
    });

    expectError(result);
    expect(await countClaims()).toBe(0);
  });

  it('stores XSS payloads as plain text and returns them via activate', async () => {
    await applyPolicy();
    const payload = '<script>alert("xss")</script>';

    const upsert = expectSuccess(
      await dispatchTool('pce_memory_upsert', {
        text: payload,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        provenance: validProvenance(),
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task', 'tool:contact-lookup'],
        q: payload,
        top_k: 10,
      })
    );

    const claims = activate.claims as Array<{ claim: { id: string; text: string } }>;
    expect(claims).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          claim: expect.objectContaining({ id: upsert.id, text: payload }),
        }),
      ])
    );
  });

  it('rejects raw path traversal in observe source_id', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_observe', {
      source_type: 'file',
      source_id: '../../etc/passwd',
      content: 'path traversal attempt',
      extract: { mode: 'noop' },
    });

    const error = expectError(result);
    expect(error.message).toContain('path traversal');
  });

  it('rejects encoded path traversal in observe source_id', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_observe', {
      source_type: 'file',
      source_id: '..%2F..%2Fsecret.txt',
      content: 'encoded path traversal attempt',
      extract: { mode: 'noop' },
    });

    const error = expectError(result);
    expect(error.message).toContain('path traversal');
  });

  it('rejects oversized durable payloads', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'x'.repeat(5001),
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: validProvenance(),
    });

    expectError(result);
    expect(await countClaims()).toBe(0);
  });
});

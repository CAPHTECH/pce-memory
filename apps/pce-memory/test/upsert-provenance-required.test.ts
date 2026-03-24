import { beforeEach, describe, expect, it } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { handleUpsert } from '../src/core/handlers';
import { applyPolicyOp, resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';
import * as E from 'fp-ts/Either';

async function setupWithPolicy() {
  await resetDbAsync();
  resetMemoryState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  const result = await applyPolicyOp()();
  expect(E.isRight(result)).toBe(true);
}

beforeEach(async () => {
  await setupWithPolicy();
});

describe('handleUpsert provenance requirements', () => {
  it('allows session claims without provenance', async () => {
    const result = await handleUpsert({
      text: 'session claim without provenance',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
    });

    expect(result.isError).toBeUndefined();
    expect(result.structuredContent?.id).toBeDefined();
  });

  it('allows session claims with provenance object lacking at', async () => {
    const result = await handleUpsert({
      text: 'session claim with partial provenance',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      provenance: { actor: 'claude' },
    });

    expect(result.isError).toBeUndefined();
    expect(result.structuredContent?.id).toBeDefined();
  });

  it('rejects project claims without provenance', async () => {
    const result = await handleUpsert({
      text: 'project claim without provenance',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toBe(
      'provenance.at is required for non-session scope claims'
    );
  });

  it('rejects principle claims without provenance', async () => {
    const result = await handleUpsert({
      text: 'principle claim without provenance',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'internal',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toBe(
      'provenance.at is required for non-session scope claims'
    );
  });

  it('allows project claims when provenance.at is present', async () => {
    const result = await handleUpsert({
      text: 'project claim with provenance',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    expect(result.isError).toBeUndefined();
    expect(result.structuredContent?.id).toBeDefined();
  });

  it('rejects project claims when provenance.at is missing', async () => {
    const result = await handleUpsert({
      text: 'project claim with incomplete provenance',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenance: { actor: 'claude' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toBe(
      'provenance.at is required for non-session scope claims'
    );
  });
});

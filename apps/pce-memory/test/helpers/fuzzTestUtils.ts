/**
 * Shared helpers for fuzz & boundary value tests.
 */
import { expect } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../../src/core/handlers';
import { initDb, initSchema, resetDbAsync } from '../../src/db/connection';
import { resetLayerScopeState } from '../../src/state/layerScopeState';
import { resetMemoryState } from '../../src/state/memoryState';
import { initRateState, resetRates } from '../../src/store/rate';

export { computeContentHash };
export { dispatchTool };

export function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

export function validProvenance(msOffset: number = -60_000) {
  return { at: isoOffset(msOffset), actor: 'claude' };
}

export async function setupRuntime() {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env['PCE_DB'] = ':memory:';
  process.env['PCE_RATE_CAP'] = '10000';
  delete process.env['PCE_OBS_MAX_BYTES'];
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

export function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError ?? false).toBe(false);
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

export function expectError(
  result: Awaited<ReturnType<typeof dispatchTool>>,
  expectedCode?: string
) {
  expect(result.isError).toBe(true);
  if (expectedCode) {
    expect(result.structuredContent?.error?.code).toBe(expectedCode);
  }
  return result.structuredContent?.error as { code: string; message: string };
}

export async function applyPolicy() {
  const result = await dispatchTool('pce_memory_policy_apply', {});
  expectSuccess(result);
}

export function validUpsertArgs(text?: string) {
  const t = text ?? `test-${crypto.randomUUID()}`;
  return {
    text: t,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: `sha256:${computeContentHash(t)}`,
    provenance: validProvenance(),
  };
}

export async function createClaim(text?: string) {
  const args = validUpsertArgs(text);
  const result = await dispatchTool('pce_memory_upsert', args);
  return expectSuccess(result);
}

export async function createObservation(content?: string) {
  const c = content ?? `obs-${crypto.randomUUID()}`;
  const result = await dispatchTool('pce_memory_observe', {
    source_type: 'chat',
    content: c,
    boundary_class: 'internal',
    extract: { mode: 'noop' },
  });
  return expectSuccess(result);
}

export async function createPendingCandidate() {
  const obs = await createObservation();
  const distill = await dispatchTool('pce_memory_distill', {
    source_observation_ids: [obs.observation_id],
    note: 'fuzz test candidate',
  });
  return expectSuccess(distill);
}

export async function createPromotedClaim() {
  const candidate = await createPendingCandidate();
  const promote = await dispatchTool('pce_memory_promote', {
    candidate_id: candidate.candidate_id,
    provenance: validProvenance(),
  });
  return { candidate, promote: expectSuccess(promote) };
}

export async function createActivatedState() {
  const claim = await createClaim();
  const activate = await dispatchTool('pce_memory_activate', {
    q: 'test',
    scope: ['project'],
    allow: ['answer:task'],
    top_k: 10,
  });
  expectSuccess(activate);
  return claim;
}

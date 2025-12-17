/**
 * content_hash検証テスト
 * upsert時にcontent_hashがtextの実際のSHA256と一致することを検証
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { initRateState, resetRates } from '../src/store/rate';
import { handleUpsert } from '../src/core/handlers';
import { applyPolicyOp, resetMemoryState } from '../src/state/memoryState';
import { computeContentHash } from '@pce/embeddings';
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

describe('handleUpsert content_hash validation', () => {
  it('accepts valid content_hash matching text SHA256', async () => {
    const text = 'Test claim text';
    const correctHash = `sha256:${computeContentHash(text)}`;

    const result = await handleUpsert({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: correctHash,
    });

    expect(result.isError).toBeUndefined();
    const response = JSON.parse(result.content[0]!.text);
    expect(response.id).toBeDefined();
  });

  it('rejects content_hash that does not match text SHA256', async () => {
    const text = 'Test claim text';
    const wrongHash = 'sha256:a7b3c5d9e1f2a4b6c8d0e2f4a6b8c0d2e4f6a8b0c2d4e6f8a0b2c4d6e8f0a2b4';

    const result = await handleUpsert({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: wrongHash,
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('VALIDATION_ERROR');
    expect(response.error.message).toContain('content_hash mismatch');
  });

  it('rejects dummy hash patterns', async () => {
    const text = 'Real content';
    // Dummy pattern: sequential hex characters
    const dummyHash = 'sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef';

    const result = await handleUpsert({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: dummyHash,
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.code).toBe('VALIDATION_ERROR');
    expect(response.error.message).toContain('content_hash mismatch');
  });

  it('error message includes expected and actual hash', async () => {
    const text = 'Test content for hash comparison';
    const expectedHash = `sha256:${computeContentHash(text)}`;
    const wrongHash = 'sha256:aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa';

    const result = await handleUpsert({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: wrongHash,
    });

    expect(result.isError).toBe(true);
    const response = JSON.parse(result.content[0]!.text);
    expect(response.error.message).toContain(expectedHash);
    expect(response.error.message).toContain(wrongHash);
  });
});

import { describe, it, expect, beforeEach } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../src/core/handlers';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe('activate usage learning', () => {
  it('increments retrieval_count and stamps last_retrieved_at for returned durable claims', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const text = 'usage learning durable claim';
    const upsertResult = await dispatchTool('pce_memory_upsert', {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: { at: '2026-03-25T00:00:00.000Z' },
    });
    const claimId = upsertResult.structuredContent?.id as string;

    const firstActivate = await dispatchTool('pce_memory_activate', {
      q: 'usage learning durable',
      scope: ['project'],
      allow: ['answer:task'],
    });
    const firstClaims = firstActivate.structuredContent?.claims as Array<{
      claim: { id: string; retrieval_count?: number; last_retrieved_at?: string | null };
    }>;
    const activatedClaim = firstClaims.find((item) => item.claim.id === claimId)?.claim;
    expect(activatedClaim?.retrieval_count).toBe(1);
    expect(typeof activatedClaim?.last_retrieved_at).toBe('string');

    const conn = await getConnection();
    const firstReader = await conn.runAndReadAll(
      'SELECT retrieval_count, last_retrieved_at FROM claims WHERE id = $1',
      [claimId]
    );
    const firstRows = firstReader.getRowObjects() as Array<{
      retrieval_count: number | bigint;
      last_retrieved_at: string | null;
    }>;
    expect(Number(firstRows[0]?.retrieval_count ?? 0)).toBe(1);
    expect(typeof firstRows[0]?.last_retrieved_at).toBe('string');

    await dispatchTool('pce_memory_activate', {
      q: 'usage learning durable',
      scope: ['project'],
      allow: ['answer:task'],
    });

    const secondReader = await conn.runAndReadAll(
      'SELECT retrieval_count, last_retrieved_at FROM claims WHERE id = $1',
      [claimId]
    );
    const secondRows = secondReader.getRowObjects() as Array<{
      retrieval_count: number | bigint;
      last_retrieved_at: string | null;
    }>;
    expect(Number(secondRows[0]?.retrieval_count ?? 0)).toBe(2);
    expect(typeof secondRows[0]?.last_retrieved_at).toBe('string');
  });
});

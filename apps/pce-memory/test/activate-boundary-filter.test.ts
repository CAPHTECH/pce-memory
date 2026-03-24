import { describe, it, expect, beforeEach } from 'vitest';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { dispatchTool } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';
import { upsertClaim } from '../src/store/claims';
import { updateCritic } from '../src/store/critic';
import { computeContentHash } from '@pce/embeddings';

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

describe('activate boundary filter', () => {
  it('allowに基づきboundary_classでフィルタされる', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const internalText = 'internal claim';
    const internal = await dispatchTool('pce_memory_upsert', {
      text: internalText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(internalText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const piiText = 'pii claim';
    const pii = await dispatchTool('pce_memory_upsert', {
      text: piiText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'pii',
      content_hash: `sha256:${computeContentHash(piiText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const secretText = 'preexisting secret claim';
    const { claim: secret } = await upsertClaim({
      text: secretText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: `sha256:${computeContentHash(secretText)}`,
    });

    const internalId = internal.structuredContent?.id as string;
    const piiId = pii.structuredContent?.id as string;
    const secretId = secret.id;

    const ac1 = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      include_meta: false,
    });
    const claims1 = (ac1.structuredContent?.claims as any[]).map((x) => x?.claim?.id);
    expect(claims1).toContain(internalId);
    expect(claims1).not.toContain(piiId);
    expect(claims1).not.toContain(secretId);

    const ac2 = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['tool:contact-lookup'],
      include_meta: false,
    });
    const claims2 = (ac2.structuredContent?.claims as any[]).map((x) => x?.claim?.id);
    expect(claims2).toContain(internalId);
    expect(claims2).toContain(piiId);
    expect(claims2).not.toContain(secretId);
  });

  it('top_k と pagination metadata が boundary filter 後の集合を反映する', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const internalOneText = 'internal first allowed claim';
    const internalOne = await dispatchTool('pce_memory_upsert', {
      text: internalOneText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(internalOneText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const internalTwoText = 'internal second allowed claim';
    const internalTwo = await dispatchTool('pce_memory_upsert', {
      text: internalTwoText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(internalTwoText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const internalThreeText = 'internal third allowed claim';
    const internalThree = await dispatchTool('pce_memory_upsert', {
      text: internalThreeText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(internalThreeText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const piiText = 'pii disallowed top score claim';
    const pii = await dispatchTool('pce_memory_upsert', {
      text: piiText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'pii',
      content_hash: `sha256:${computeContentHash(piiText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    const internalOneId = internalOne.structuredContent?.id as string;
    const internalTwoId = internalTwo.structuredContent?.id as string;
    const internalThreeId = internalThree.structuredContent?.id as string;
    const piiId = pii.structuredContent?.id as string;

    await updateCritic(internalOneId, 0.7, 0, 1);
    await updateCritic(internalTwoId, 0.6, 0, 1);
    await updateCritic(internalThreeId, 0.5, 0, 1);
    await updateCritic(piiId, 0.95, 0, 1);

    const page1 = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 1,
      include_meta: false,
    });
    const claims1 = page1.structuredContent?.claims as any[];
    expect(claims1).toHaveLength(1);
    expect(claims1[0]?.claim?.id).toBe(internalOneId);
    expect(claims1[0]?.claim?.id).not.toBe(piiId);
    expect(page1.structuredContent?.next_cursor).toBe(internalOneId);
    expect(page1.structuredContent?.has_more).toBe(true);

    const page2 = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 1,
      cursor: page1.structuredContent?.next_cursor,
      include_meta: false,
    });
    const claims2 = page2.structuredContent?.claims as any[];
    expect(claims2).toHaveLength(1);
    expect(claims2[0]?.claim?.id).toBe(internalTwoId);
    expect(claims2[0]?.claim?.id).not.toBe(piiId);
    expect(page2.structuredContent?.next_cursor).toBe(internalTwoId);
    expect(page2.structuredContent?.has_more).toBe(true);

    const page3 = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 1,
      cursor: page2.structuredContent?.next_cursor,
      include_meta: false,
    });
    const claims3 = page3.structuredContent?.claims as any[];
    expect(claims3).toHaveLength(1);
    expect(claims3[0]?.claim?.id).toBe(internalThreeId);
    expect(claims3[0]?.claim?.id).not.toBe(piiId);
    expect(page3.structuredContent?.next_cursor).toBeUndefined();
    expect(page3.structuredContent?.has_more).toBe(false);
  });

  it('secret boundary_class の upsert を拒否する', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const secretText = 'secret claim';
    const result = await dispatchTool('pce_memory_upsert', {
      text: secretText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: `sha256:${computeContentHash(secretText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain(
      "boundary_class 'secret' is rejected by default"
    );
    expect(result.structuredContent?.error?.message).toContain('pce_memory_observe');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT COUNT(*)::INTEGER AS cnt FROM claims');
    const rows = reader.getRowObjects() as { cnt: number }[];
    expect(rows[0]?.cnt).toBe(0);
  });

  it('secret rejection が content_hash mismatch より優先される', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const result = await dispatchTool('pce_memory_upsert', {
      text: 'secret claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: `sha256:${'0'.repeat(64)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain(
      "boundary_class 'secret' is rejected by default"
    );
    expect(result.structuredContent?.error?.message).not.toContain('content_hash mismatch');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT COUNT(*)::INTEGER AS cnt FROM claims');
    const rows = reader.getRowObjects() as { cnt: number }[];
    expect(rows[0]?.cnt).toBe(0);
  });
});

import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { dispatchTool } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';
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
      scope: 'session',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(internalText)}`,
    });
    const piiText = 'pii claim';
    const pii = await dispatchTool('pce_memory_upsert', {
      text: piiText,
      kind: 'fact',
      scope: 'session',
      boundary_class: 'pii',
      content_hash: `sha256:${computeContentHash(piiText)}`,
    });
    const secretText = 'secret claim';
    const secret = await dispatchTool('pce_memory_upsert', {
      text: secretText,
      kind: 'fact',
      scope: 'session',
      boundary_class: 'secret',
      content_hash: `sha256:${computeContentHash(secretText)}`,
    });

    const internalId = internal.structuredContent?.id as string;
    const piiId = pii.structuredContent?.id as string;
    const secretId = secret.structuredContent?.id as string;

    const ac1 = await dispatchTool('pce_memory_activate', {
      scope: ['session'],
      allow: ['answer:task'],
      include_meta: false,
    });
    const claims1 = (ac1.structuredContent?.claims as any[]).map((x) => x?.claim?.id);
    expect(claims1).toContain(internalId);
    expect(claims1).not.toContain(piiId);
    expect(claims1).not.toContain(secretId);

    const ac2 = await dispatchTool('pce_memory_activate', {
      scope: ['session'],
      allow: ['tool:contact-lookup'],
      include_meta: false,
    });
    const claims2 = (ac2.structuredContent?.claims as any[]).map((x) => x?.claim?.id);
    expect(claims2).toContain(internalId);
    expect(claims2).toContain(piiId);
    expect(claims2).not.toContain(secretId);
  });
});

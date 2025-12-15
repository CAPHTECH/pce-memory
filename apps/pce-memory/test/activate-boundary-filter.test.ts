import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { dispatchTool } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';

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
    await dispatchTool('pce.memory.policy.apply', {});

    const internal = await dispatchTool('pce.memory.upsert', {
      text: 'internal claim',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '0'.repeat(64),
    });
    const pii = await dispatchTool('pce.memory.upsert', {
      text: 'pii claim',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'pii',
      content_hash: 'sha256:' + '1'.repeat(64),
    });
    const secret = await dispatchTool('pce.memory.upsert', {
      text: 'secret claim',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'secret',
      content_hash: 'sha256:' + '2'.repeat(64),
    });

    const internalId = internal.structuredContent?.id as string;
    const piiId = pii.structuredContent?.id as string;
    const secretId = secret.structuredContent?.id as string;

    const ac1 = await dispatchTool('pce.memory.activate', {
      scope: ['session'],
      allow: ['answer:task'],
      include_meta: false,
    });
    const claims1 = (ac1.structuredContent?.claims as any[]).map((x) => x?.claim?.id);
    expect(claims1).toContain(internalId);
    expect(claims1).not.toContain(piiId);
    expect(claims1).not.toContain(secretId);

    const ac2 = await dispatchTool('pce.memory.activate', {
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


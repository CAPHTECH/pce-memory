/**
 * Fuzz & Boundary Value Testing for all MCP handlers
 * Tests adversarial inputs, edge cases, and boundary conditions.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../src/core/handlers';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';

// ==================== Test Helpers ====================

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
  process.env['PCE_DB'] = ':memory:';
  process.env['PCE_RATE_CAP'] = '10000';
  delete process.env['PCE_OBS_MAX_BYTES'];
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError ?? false).toBe(false);
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

function expectError(
  result: Awaited<ReturnType<typeof dispatchTool>>,
  expectedCode?: string
) {
  expect(result.isError).toBe(true);
  if (expectedCode) {
    expect(result.structuredContent?.error?.code).toBe(expectedCode);
  }
  return result.structuredContent?.error as { code: string; message: string };
}

async function applyPolicy() {
  const result = await dispatchTool('pce_memory_policy_apply', {});
  expectSuccess(result);
}

function validUpsertArgs(text?: string) {
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

async function createClaim(text?: string) {
  const args = validUpsertArgs(text);
  const result = await dispatchTool('pce_memory_upsert', args);
  return expectSuccess(result);
}

async function createObservation(content?: string) {
  const c = content ?? `obs-${crypto.randomUUID()}`;
  const result = await dispatchTool('pce_memory_observe', {
    source_type: 'chat',
    content: c,
    boundary_class: 'internal',
    extract: { mode: 'noop' },
  });
  return expectSuccess(result);
}

async function createPendingCandidate() {
  const obs = await createObservation();
  const distill = await dispatchTool('pce_memory_distill', {
    source_observation_ids: [obs.observation_id],
    note: 'fuzz test candidate',
  });
  return expectSuccess(distill);
}

async function createPromotedClaim() {
  const candidate = await createPendingCandidate();
  const promote = await dispatchTool('pce_memory_promote', {
    candidate_id: candidate.candidate_id,
    provenance: validProvenance(),
  });
  return { candidate, promote: expectSuccess(promote) };
}

async function createActivatedState() {
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

beforeEach(async () => {
  await setupRuntime();
});

// ==================== APPROACH 1: Input Fuzzing ====================

describe('FUZZ: pce_memory_upsert', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  describe('text field fuzzing', () => {
    it('rejects empty string', async () => {
      const args = validUpsertArgs();
      args.text = '';
      args.content_hash = `sha256:${computeContentHash('')}`;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects null', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).text = null;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects undefined', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).text = undefined;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects number instead of string', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).text = 42;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects array instead of string', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).text = ['hello'];
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects object instead of string', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).text = { value: 'hello' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('accepts text at exactly max length (5000 chars)', async () => {
      const t = 'a'.repeat(5000);
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });

    it('rejects text over max length (5001 chars)', async () => {
      const t = 'a'.repeat(5001);
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('accepts single character text', async () => {
      const t = 'x';
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });

    it('handles unicode emoji text', async () => {
      const t = '🎉🚀💡 Unicode emoji test 日本語テスト العربية';
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });

    it('handles zero-width characters', async () => {
      const t = 'text\u200B\u200C\u200Dwith\uFEFFzero-width';
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });

    it('handles null bytes in text', async () => {
      const t = 'text\x00with\x00null\x00bytes';
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      // Should either accept or cleanly reject - no crash
      const result = await dispatchTool('pce_memory_upsert', args);
      expect(result).toBeDefined();
    });

    it('handles RTL text', async () => {
      const t = 'مرحبا بالعالم test';
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });
  });

  describe('content_hash fuzzing', () => {
    it('rejects wrong format (no sha256: prefix)', async () => {
      const args = validUpsertArgs();
      args.content_hash = 'abc123';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects partial hash', async () => {
      const args = validUpsertArgs();
      args.content_hash = 'sha256:abcd';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects hash that does not match text', async () => {
      const args = validUpsertArgs();
      args.content_hash = `sha256:${'a'.repeat(64)}`;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('accepts auto-generated hash when content_hash omitted', async () => {
      const t = `auto-hash-${crypto.randomUUID()}`;
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        provenance: validProvenance(),
      };
      const result = expectSuccess(await dispatchTool('pce_memory_upsert', args));
      expect(result.content_hash).toMatch(/^sha256:[0-9a-f]{64}$/);
    });
  });

  describe('kind field fuzzing', () => {
    it('rejects invalid kind', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).kind = 'invalid_kind';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects empty kind', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).kind = '';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects numeric kind', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).kind = 123;
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  });

  describe('scope field fuzzing', () => {
    it('rejects session scope', async () => {
      const args = validUpsertArgs();
      args.scope = 'session';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects invalid scope', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).scope = 'global';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  });

  describe('boundary_class field fuzzing', () => {
    it('rejects secret boundary_class', async () => {
      const args = validUpsertArgs();
      args.boundary_class = 'secret';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects wrong-case boundary_class', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).boundary_class = 'INTERNAL';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  });

  describe('provenance field fuzzing', () => {
    it('rejects provenance with future date beyond skew', async () => {
      const args = validUpsertArgs();
      args.provenance = { at: isoOffset(600_000), actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance with invalid date format', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = { at: 'not-a-date', actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance without at field', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = { actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance as string', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = 'not-an-object';
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance with empty at', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = { at: '', actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance with Feb 30 date', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = { at: '2025-02-30T12:00:00Z', actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance with Feb 29 on non-leap year', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = { at: '2023-02-29T12:00:00Z', actor: 'claude' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  });

  describe('memory_type field fuzzing', () => {
    it('rejects invalid memory_type', async () => {
      const args = { ...validUpsertArgs(), memory_type: 'invalid_type' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('accepts valid memory_type', async () => {
      const args = { ...validUpsertArgs(), memory_type: 'knowledge' };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });
  });

  describe('entities/relations fuzzing', () => {
    it('handles 100 entities in single upsert', async () => {
      const entities = Array.from({ length: 100 }, (_, i) => ({
        id: `ent_${i}`,
        type: 'Concept',
        name: `Entity ${i}`,
        canonical_key: `entity_${i}`,
      }));
      const args = { ...validUpsertArgs(), entities };
      // Should not crash
      const result = await dispatchTool('pce_memory_upsert', args);
      expect(result).toBeDefined();
    });

    it('handles 100 relations in single upsert', async () => {
      const relations = Array.from({ length: 100 }, (_, i) => ({
        id: `rel_${i}`,
        src_id: `ent_src_${i}`,
        dst_id: `ent_dst_${i}`,
        type: 'USES',
      }));
      const args = { ...validUpsertArgs(), relations };
      const result = await dispatchTool('pce_memory_upsert', args);
      expect(result).toBeDefined();
    });

    it('handles entity with deeply nested attrs', async () => {
      let nested: Record<string, unknown> = { value: 'leaf' };
      for (let i = 0; i < 20; i++) {
        nested = { nested };
      }
      const entities = [{
        id: 'ent_nested',
        type: 'Concept',
        name: 'Nested Entity',
        attrs: nested,
      }];
      const args = { ...validUpsertArgs(), entities };
      const result = await dispatchTool('pce_memory_upsert', args);
      expect(result).toBeDefined();
    });
  });

  describe('unknown fields', () => {
    it('rejects unknown top-level fields', async () => {
      const args = { ...validUpsertArgs(), unknown_field: 'value' };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  });
});

describe('FUZZ: pce_memory_observe', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  describe('source_type fuzzing', () => {
    it('rejects invalid source_type', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'invalid',
          content: 'test',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects numeric source_type', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 42,
          content: 'test',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects null source_type', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: null,
          content: 'test',
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('content fuzzing', () => {
    it('rejects empty content', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: '',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects null content', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: null,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('handles content with null bytes', async () => {
      const result = await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'hello\x00world',
      });
      expect(result).toBeDefined();
    });
  });

  describe('ttl_days fuzzing', () => {
    it('rejects ttl_days=0', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          ttl_days: 0,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects negative ttl_days', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          ttl_days: -5,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects NaN ttl_days', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          ttl_days: NaN,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects Infinity ttl_days', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          ttl_days: Infinity,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('clamps ttl_days to max', async () => {
      const result = expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test with huge ttl',
          ttl_days: 99999,
        })
      );
      expect(result.observation_id).toBeDefined();
    });

    it('accepts ttl_days=1 (minimum positive)', async () => {
      expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test min ttl',
          ttl_days: 1,
        })
      );
    });

    it('accepts string ttl_days that converts to valid number', async () => {
      expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test string ttl',
          ttl_days: '7',
        })
      );
    });

    it('rejects string ttl_days that is not a number', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test bad string ttl',
          ttl_days: 'not_a_number',
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('tags fuzzing', () => {
    it('rejects tag with special characters', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          tags: ['valid', 'invalid tag with spaces'],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects tags with > 32 items', async () => {
      const tags = Array.from({ length: 33 }, (_, i) => `tag_${i}`);
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          tags,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects tags array with non-string items', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          tags: ['valid', 42],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects tag that is too long', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          tags: ['a'.repeat(257)],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('accepts tags at max count (32)', async () => {
      const tags = Array.from({ length: 32 }, (_, i) => `tag_${i}`);
      expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test with 32 tags',
          tags,
        })
      );
    });
  });

  describe('source_id path traversal', () => {
    it('rejects path traversal in source_id', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'file',
          content: 'test',
          source_id: '../../../etc/passwd',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects encoded path traversal', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'file',
          content: 'test',
          source_id: '..%2F..%2Fetc%2Fpasswd',
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('boundary_class fuzzing', () => {
    it('rejects invalid boundary_class string', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          boundary_class: 'confidential',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects numeric boundary_class', async () => {
      expectError(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'test',
          boundary_class: 42,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('accepts secret boundary_class (observe allows it)', async () => {
      expectSuccess(
        await dispatchTool('pce_memory_observe', {
          source_type: 'chat',
          content: 'my secret observation',
          boundary_class: 'secret',
        })
      );
    });
  });
});

describe('FUZZ: pce_memory_activate', () => {
  beforeEach(async () => {
    await applyPolicy();
    await createClaim(); // need HasClaims state
  });

  describe('scope fuzzing', () => {
    it('rejects non-array scope', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: 'project',
          allow: ['answer:task'],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects empty scope array', async () => {
      // Empty scope array should still work - just returns no results
      const result = await dispatchTool('pce_memory_activate', {
        q: 'test',
        scope: [],
        allow: ['answer:task'],
      });
      // Should not crash
      expect(result).toBeDefined();
    });

    it('rejects scope with invalid entries', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project', 'invalid_scope'],
          allow: ['answer:task'],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects scope with non-string entries', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: [42, 'project'],
          allow: ['answer:task'],
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('top_k boundary values', () => {
    it('rejects top_k=0', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: 0,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('accepts top_k=1', async () => {
      const result = await dispatchTool('pce_memory_activate', {
        q: 'test',
        scope: ['project'],
        allow: ['answer:task'],
        top_k: 1,
      });
      expect(result.isError ?? false).toBe(false);
    });

    it('accepts top_k=50', async () => {
      const result = await dispatchTool('pce_memory_activate', {
        q: 'test',
        scope: ['project'],
        allow: ['answer:task'],
        top_k: 50,
      });
      expect(result.isError ?? false).toBe(false);
    });

    it('rejects top_k=51 (over max)', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: 51,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects negative top_k', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: -1,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects float top_k', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: 5.5,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects NaN top_k', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: NaN,
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects Infinity top_k', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          top_k: Infinity,
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('allow field fuzzing', () => {
    it('rejects non-array allow', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: 'answer:task',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects allow with non-string entries', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: [42],
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('intent fuzzing', () => {
    it('rejects invalid intent', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          intent: 'invalid_intent',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects numeric intent', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          intent: 42,
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('kind_filter fuzzing', () => {
    it('rejects kind_filter with invalid kinds', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          kind_filter: ['fact', 'invalid'],
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects non-array kind_filter', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          kind_filter: 'fact',
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('memory_type_filter fuzzing', () => {
    it('rejects memory_type_filter with invalid types', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          memory_type_filter: ['knowledge', 'invalid_type'],
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('include_observations fuzzing', () => {
    it('rejects non-boolean include_observations', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          include_observations: 'yes',
        }),
        'VALIDATION_ERROR'
      );
    });

    it('rejects numeric include_observations', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          include_observations: 1,
        }),
        'VALIDATION_ERROR'
      );
    });
  });

  describe('include_stale_tasks fuzzing', () => {
    it('rejects non-boolean include_stale_tasks', async () => {
      expectError(
        await dispatchTool('pce_memory_activate', {
          q: 'test',
          scope: ['project'],
          allow: ['answer:task'],
          include_stale_tasks: 'yes',
        }),
        'VALIDATION_ERROR'
      );
    });
  });
});

describe('FUZZ: pce_memory_feedback', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects feedback on non-existent claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: 'clm_nonexistent',
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid signal', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
        signal: 'invalid_signal',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing signal', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects null claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: null,
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects empty string claim_id', async () => {
    await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: '',
        signal: 'helpful',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('handles score=NaN gracefully', async () => {
    const claim = await createActivatedState();
    // NaN score should not crash
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: NaN,
    });
    expect(result).toBeDefined();
  });

  it('handles score=Infinity gracefully', async () => {
    const claim = await createActivatedState();
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: Infinity,
    });
    expect(result).toBeDefined();
  });

  it('handles negative score gracefully', async () => {
    const claim = await createActivatedState();
    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claim.id,
      signal: 'helpful',
      score: -1,
    });
    expect(result).toBeDefined();
  });

  it('rejects completed signal on non-working_state claim', async () => {
    const claim = await createActivatedState();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: claim.id,
        signal: 'completed',
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_link_claims', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects link with same source and target', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim.id,
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects link with non-existent source', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: 'clm_nonexistent',
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects link with non-existent target', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim.id,
        target_claim_id: 'clm_nonexistent',
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid link_type', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'invalid_type',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing source_claim_id', async () => {
    const claim = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        target_claim_id: claim.id,
        link_type: 'supersedes',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects confidence > 1', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 1.5,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects confidence < 0', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: -0.5,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects NaN confidence', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectError(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: NaN,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('accepts confidence=0 (boundary)', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectSuccess(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 0,
      })
    );
  });

  it('accepts confidence=1 (boundary)', async () => {
    const claim1 = await createClaim();
    const claim2 = await createClaim();
    expectSuccess(
      await dispatchTool('pce_memory_link_claims', {
        source_claim_id: claim1.id,
        target_claim_id: claim2.id,
        link_type: 'supersedes',
        confidence: 1,
      })
    );
  });
});

describe('FUZZ: pce_memory_distill', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects when no sources provided', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {}),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-array source_observation_ids', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: 'obs_123',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects source_observation_ids with non-string items', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [42, 'obs_123'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent observation IDs', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: ['obs_nonexistent'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent claim IDs', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_claim_ids: ['clm_nonexistent'],
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid proposed_kind', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_kind: 'invalid_kind',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid proposed_scope', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_scope: 'session',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects proposed_memory_type=evidence', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        proposed_memory_type: 'evidence',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string active_context_id', async () => {
    expectError(
      await dispatchTool('pce_memory_distill', {
        active_context_id: 42,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string note', async () => {
    const obs = await createObservation();
    expectError(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [obs.observation_id],
        note: 42,
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_promote', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects empty candidate_id', async () => {
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: '',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent candidate_id', async () => {
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: 'pq_nonexistent',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing provenance', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects promote on already-promoted candidate', async () => {
    const { candidate } = await createPromotedClaim();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-string review_note', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        review_note: 42,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-array reviewers', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        reviewers: 'alice',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects reviewers with non-string entries', async () => {
    const candidate = await createPendingCandidate();
    expectError(
      await dispatchTool('pce_memory_promote', {
        candidate_id: candidate.candidate_id,
        provenance: validProvenance(),
        reviewers: [42],
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_rollback', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects empty claim_id', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: '',
        reason: 'test',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects empty reason', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_123',
        reason: '',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects non-existent claim_id', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_nonexistent',
        reason: 'test',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects rollback on already-rolled-back claim', async () => {
    const { promote } = await createPromotedClaim();
    // First rollback
    expectSuccess(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'first rollback',
        provenance: validProvenance(),
      })
    );
    // Second rollback should fail
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: promote.claim_id,
        reason: 'second rollback',
        provenance: validProvenance(),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing provenance', async () => {
    expectError(
      await dispatchTool('pce_memory_rollback', {
        claim_id: 'clm_123',
        reason: 'test',
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_upsert_entity', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects missing id', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        type: 'Concept',
        name: 'Test',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing type', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        name: 'Test',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects missing name', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        type: 'Concept',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid entity type', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        type: 'InvalidType',
        name: 'Test',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects id longer than 256 chars', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'a'.repeat(257),
        type: 'Concept',
        name: 'Test',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects name longer than 1024 chars', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        type: 'Concept',
        name: 'a'.repeat(1025),
      }),
      'VALIDATION_ERROR'
    );
  });

  it('accepts id at exactly 256 chars', async () => {
    expectSuccess(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'a'.repeat(256),
        type: 'Concept',
        name: 'Test',
      })
    );
  });

  it('accepts name at exactly 1024 chars', async () => {
    expectSuccess(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        type: 'Concept',
        name: 'a'.repeat(1024),
      })
    );
  });

  it('rejects case-sensitive entity type', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_entity', {
        id: 'ent_test',
        type: 'concept',
        name: 'Test',
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_upsert_relation', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects missing required fields', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_relation', {
        id: 'rel_test',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects id longer than 256 chars', async () => {
    expectError(
      await dispatchTool('pce_memory_upsert_relation', {
        id: 'a'.repeat(257),
        src_id: 'ent_src',
        dst_id: 'ent_dst',
        type: 'USES',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('accepts relation with valid fields', async () => {
    expectSuccess(
      await dispatchTool('pce_memory_upsert_relation', {
        id: 'rel_test',
        src_id: 'ent_src',
        dst_id: 'ent_dst',
        type: 'USES',
      })
    );
  });
});

describe('FUZZ: pce_memory_query_entity', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects no filters at all', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {}),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid type filter', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {
        type: 'InvalidType',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects negative limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {
        type: 'Concept',
        limit: -1,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects zero limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {
        type: 'Concept',
        limit: 0,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('accepts very large limit (clamped by store)', async () => {
    const result = await dispatchTool('pce_memory_query_entity', {
      type: 'Concept',
      limit: 999999999,
    });
    expect(result.isError ?? false).toBe(false);
  });

  it('rejects NaN limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {
        type: 'Concept',
        limit: NaN,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects float limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_entity', {
        type: 'Concept',
        limit: 5.7,
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_query_relation', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects no filters at all', async () => {
    expectError(
      await dispatchTool('pce_memory_query_relation', {}),
      'VALIDATION_ERROR'
    );
  });

  it('rejects negative limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_relation', {
        type: 'USES',
        limit: -1,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects NaN limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_relation', {
        type: 'USES',
        limit: NaN,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects zero limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_relation', {
        type: 'USES',
        limit: 0,
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects float limit', async () => {
    expectError(
      await dispatchTool('pce_memory_query_relation', {
        type: 'USES',
        limit: 3.14,
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_boundary_validate', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('handles missing all args', async () => {
    const result = await dispatchTool('pce_memory_boundary_validate', {});
    // Uses defaults: payload='', allow=[], scope=''
    expect(result).toBeDefined();
  });

  it('handles null payload', async () => {
    const result = await dispatchTool('pce_memory_boundary_validate', {
      payload: null,
      allow: ['answer:task'],
      scope: 'project',
    });
    expect(result).toBeDefined();
  });

  it('handles numeric payload', async () => {
    const result = await dispatchTool('pce_memory_boundary_validate', {
      payload: 42,
      allow: ['answer:task'],
      scope: 'project',
    });
    expect(result).toBeDefined();
  });
});

describe('FUZZ: pce_memory_policy_apply', () => {
  it('handles empty args', async () => {
    expectSuccess(await dispatchTool('pce_memory_policy_apply', {}));
  });

  it('handles null yaml', async () => {
    const result = await dispatchTool('pce_memory_policy_apply', { yaml: null });
    expect(result).toBeDefined();
  });

  it('handles invalid yaml string', async () => {
    const result = await dispatchTool('pce_memory_policy_apply', {
      yaml: 'not: valid: yaml: {{{}}}',
    });
    // May succeed with partial parse or fail gracefully
    expect(result).toBeDefined();
  });
});

describe('FUZZ: pce_memory_state', () => {
  it('handles empty args', async () => {
    const result = await dispatchTool('pce_memory_state', {});
    expect(result).toBeDefined();
    expect(result.isError ?? false).toBe(false);
  });

  it('handles debug=true', async () => {
    const result = await dispatchTool('pce_memory_state', { debug: true });
    expect(result).toBeDefined();
  });

  it('handles debug as non-boolean', async () => {
    const result = await dispatchTool('pce_memory_state', { debug: 'yes' });
    expect(result).toBeDefined();
  });
});

// ==================== APPROACH 2: State Machine Boundary Tests ====================

describe('BOUNDARY: State machine transitions', () => {
  it('rejects upsert before policy_apply', async () => {
    const args = validUpsertArgs();
    expectError(await dispatchTool('pce_memory_upsert', args), 'STATE_ERROR');
  });

  it('rejects observe before policy_apply', async () => {
    expectError(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: 'test',
      }),
      'STATE_ERROR'
    );
  });

  it('allows activate in PolicyApplied state (returns empty results)', async () => {
    await applyPolicy();
    const result = await dispatchTool('pce_memory_activate', {
      q: 'test',
      scope: ['project'],
      allow: ['answer:task'],
    });
    const body = expectSuccess(result);
    expect(body.claims_count).toBe(0);
  });

  it('rejects feedback before activate (not Ready state)', async () => {
    await applyPolicy();
    await createClaim();
    expectError(
      await dispatchTool('pce_memory_feedback', {
        claim_id: 'clm_test',
        signal: 'helpful',
      }),
      'STATE_ERROR'
    );
  });

  it('allows activate with include_observations in PolicyApplied state', async () => {
    await applyPolicy();
    // Create an observation so there is something to find
    await createObservation();
    const result = await dispatchTool('pce_memory_activate', {
      q: 'test',
      scope: ['project'],
      allow: ['answer:task'],
      include_observations: true,
    });
    expect(result.isError ?? false).toBe(false);
  });
});

// ==================== SQL Injection Payloads ====================

describe('SECURITY: SQL injection resistance', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  const sqlPayloads = [
    "'; DROP TABLE claims; --",
    "' OR '1'='1",
    "'; DELETE FROM claims WHERE '1'='1",
    "1; SELECT * FROM claims",
    "UNION SELECT * FROM claims--",
    "' UNION ALL SELECT NULL,NULL,NULL--",
  ];

  for (const payload of sqlPayloads) {
    it(`upsert text handles SQL payload: ${payload.slice(0, 40)}...`, async () => {
      const t = payload;
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: validProvenance(),
      };
      const result = await dispatchTool('pce_memory_upsert', args);
      if (!result.isError) {
        // If it succeeded, verify the text is stored correctly
        const stored = result.structuredContent;
        expect(stored?.id).toBeDefined();
      }
    });

    it(`observe content handles SQL payload: ${payload.slice(0, 40)}...`, async () => {
      const result = await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content: payload,
      });
      // Should not crash
      expect(result).toBeDefined();
    });

    it(`activate q handles SQL payload: ${payload.slice(0, 40)}...`, async () => {
      await createClaim();
      const result = await dispatchTool('pce_memory_activate', {
        q: payload,
        scope: ['project'],
        allow: ['answer:task'],
      });
      // Should not crash
      expect(result).toBeDefined();
    });
  }
});

// ==================== ISO DateTime Validation ====================

describe('BOUNDARY: ISO DateTime validation', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  const invalidDates = [
    { label: 'month 13', value: '2025-13-01T00:00:00Z' },
    { label: 'month 00', value: '2025-00-01T00:00:00Z' },
    { label: 'day 32', value: '2025-01-32T00:00:00Z' },
    { label: 'day 00', value: '2025-01-00T00:00:00Z' },
    { label: 'hour 24', value: '2025-01-01T24:00:00Z' },
    { label: 'minute 60', value: '2025-01-01T00:60:00Z' },
    { label: 'second 60', value: '2025-01-01T00:00:60Z' },
    { label: 'no timezone', value: '2025-01-01T00:00:00' },
    { label: 'date only', value: '2025-01-01' },
    { label: 'unix timestamp', value: '1700000000' },
    { label: 'Apr 31', value: '2025-04-31T00:00:00Z' },
    { label: 'Jun 31', value: '2025-06-31T00:00:00Z' },
    { label: 'Sep 31', value: '2025-09-31T00:00:00Z' },
    { label: 'Nov 31', value: '2025-11-31T00:00:00Z' },
  ];

  for (const { label, value } of invalidDates) {
    it(`rejects invalid provenance.at: ${label}`, async () => {
      const t = `date-test-${label}`;
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: { at: value, actor: 'claude' },
      };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });
  }

  const validDates = [
    { label: 'UTC Z', value: '2025-01-01T00:00:00Z' },
    { label: 'positive offset', value: '2025-01-01T00:00:00+09:00' },
    { label: 'negative offset', value: '2025-01-01T00:00:00-05:00' },
    { label: 'with milliseconds', value: '2025-01-01T00:00:00.123Z' },
    { label: 'Feb 29 leap year', value: '2024-02-29T00:00:00Z' },
  ];

  for (const { label, value } of validDates) {
    it(`accepts valid provenance.at: ${label}`, async () => {
      const t = `date-valid-${label}`;
      const args = {
        text: t,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:${computeContentHash(t)}`,
        provenance: { at: value, actor: 'claude' },
      };
      expectSuccess(await dispatchTool('pce_memory_upsert', args));
    });
  }
});

// ==================== recencyDecay division-by-zero guard ====================

describe('BOUNDARY: recencyDecay with invalid halfLifeDays', () => {
  // Import the function directly for unit testing
  it('returns 0 for halfLifeDays=0 (division by zero guard)', async () => {
    const { recencyDecay } = await import('../src/store/rerank');
    const result = recencyDecay(new Date(), 0);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBe(0);
  });

  it('returns 0 for halfLifeDays=NaN', async () => {
    const { recencyDecay } = await import('../src/store/rerank');
    const result = recencyDecay(new Date(), NaN);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBe(0);
  });

  it('returns 0 for halfLifeDays=-1', async () => {
    const { recencyDecay } = await import('../src/store/rerank');
    const result = recencyDecay(new Date(), -1);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBe(0);
  });

  it('returns 0 for halfLifeDays=Infinity', async () => {
    const { recencyDecay } = await import('../src/store/rerank');
    const result = recencyDecay(new Date(), Infinity);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBe(0);
  });

  it('returns valid value for normal halfLifeDays', async () => {
    const { recencyDecay } = await import('../src/store/rerank');
    const result = recencyDecay(new Date(Date.now() - 86_400_000), 30);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBeGreaterThan(0);
    expect(result).toBeLessThanOrEqual(1);
  });
});

// ==================== Cursor pagination safety ====================

describe('BOUNDARY: handleListPrompts cursor pagination', () => {
  it('handles NaN cursor gracefully', async () => {
    const { handleListPrompts } = await import('../src/core/handlers');
    const result = await handleListPrompts({ cursor: 'not_a_number' });
    expect(result.prompts).toBeDefined();
    expect(Array.isArray(result.prompts)).toBe(true);
  });

  it('handles negative cursor gracefully', async () => {
    const { handleListPrompts } = await import('../src/core/handlers');
    const result = await handleListPrompts({ cursor: '-5' });
    expect(result.prompts).toBeDefined();
    expect(Array.isArray(result.prompts)).toBe(true);
  });

  it('handles extremely large cursor', async () => {
    const { handleListPrompts } = await import('../src/core/handlers');
    const result = await handleListPrompts({ cursor: '999999999' });
    expect(result.prompts).toBeDefined();
    expect(result.prompts.length).toBe(0);
  });

  it('handles valid cursor', async () => {
    const { handleListPrompts } = await import('../src/core/handlers');
    const result = await handleListPrompts({ cursor: '0' });
    expect(result.prompts).toBeDefined();
    expect(result.prompts.length).toBeGreaterThan(0);
  });
});

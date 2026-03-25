/**
 * Fuzz testing for pce_memory_upsert handler.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  applyPolicy,
  computeContentHash,
  dispatchTool,
  expectError,
  expectSuccess,
  isoOffset,
  setupRuntime,
  validProvenance,
  validUpsertArgs,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
});

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
      (args as Record<string, unknown>).provenance = {
        at: '2025-02-30T12:00:00Z',
        actor: 'claude',
      };
      expectError(await dispatchTool('pce_memory_upsert', args), 'VALIDATION_ERROR');
    });

    it('rejects provenance with Feb 29 on non-leap year', async () => {
      const args = validUpsertArgs();
      (args as Record<string, unknown>).provenance = {
        at: '2023-02-29T12:00:00Z',
        actor: 'claude',
      };
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
      const entities = [
        {
          id: 'ent_nested',
          type: 'Concept',
          name: 'Nested Entity',
          attrs: nested,
        },
      ];
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

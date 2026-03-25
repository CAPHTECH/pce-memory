/**
 * Fuzz testing for pce_memory_observe handler.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  applyPolicy,
  dispatchTool,
  expectError,
  expectSuccess,
  setupRuntime,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
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

/**
 * Fuzz testing for pce_memory_activate handler.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  applyPolicy,
  createClaim,
  dispatchTool,
  expectError,
  setupRuntime,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
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

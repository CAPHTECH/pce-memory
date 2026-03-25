/**
 * Fuzz testing for graph handlers: upsert_entity, upsert_relation, query_entity, query_relation.
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
    expectError(await dispatchTool('pce_memory_query_entity', {}), 'VALIDATION_ERROR');
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
    expectError(await dispatchTool('pce_memory_query_relation', {}), 'VALIDATION_ERROR');
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

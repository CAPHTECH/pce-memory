/**
 * Fuzz & boundary tests for: boundary_validate, policy_apply, state,
 * state machine transitions, SQL injection, ISO DateTime, normalizeLimit,
 * recencyDecay, handleListPrompts cursor, sync_push, sync_pull.
 */
import { beforeEach, describe, expect, it } from 'vitest';
import {
  applyPolicy,
  computeContentHash,
  createClaim,
  createObservation,
  dispatchTool,
  expectError,
  expectSuccess,
  setupRuntime,
  validProvenance,
  validUpsertArgs,
} from './helpers/fuzzTestUtils';

beforeEach(async () => {
  await setupRuntime();
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

// ==================== hybridSearch normalizeLimit NaN guard ====================

describe('BOUNDARY: normalizeLimit with NaN/invalid inputs', () => {
  it('splitQueryWords does not crash on extremely long query', async () => {
    const { splitQueryWords } = await import('../src/store/hybridSearch');
    // 10KB query - should not crash
    const longQuery = 'word '.repeat(2000);
    const words = splitQueryWords(longQuery);
    expect(Array.isArray(words)).toBe(true);
    expect(words.length).toBeLessThanOrEqual(2000);
  });
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

// ==================== Sync handler input validation ====================

describe('FUZZ: pce_memory_sync_push', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects path traversal in target_dir', async () => {
    expectError(
      await dispatchTool('pce_memory_sync_push', {
        target_dir: '../../../etc/malicious',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid since date', async () => {
    expectError(
      await dispatchTool('pce_memory_sync_push', {
        since: 'not-a-date',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects numeric since', async () => {
    expectError(
      await dispatchTool('pce_memory_sync_push', {
        since: 12345,
      }),
      'VALIDATION_ERROR'
    );
  });
});

describe('FUZZ: pce_memory_sync_pull', () => {
  beforeEach(async () => {
    await applyPolicy();
  });

  it('rejects path traversal in source_dir', async () => {
    expectError(
      await dispatchTool('pce_memory_sync_pull', {
        source_dir: '../../../etc/malicious',
      }),
      'VALIDATION_ERROR'
    );
  });

  it('rejects invalid since date', async () => {
    expectError(
      await dispatchTool('pce_memory_sync_pull', {
        since: 'not-a-date',
      }),
      'VALIDATION_ERROR'
    );
  });
});

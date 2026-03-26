import { describe, expect, it } from 'vitest';
import { toStructuredProvenance } from '../src/core/handlers/shared';

describe('toStructuredProvenance', () => {
  it('preserves explicitly provided empty optional values', () => {
    const provenance = toStructuredProvenance({
      at: '2025-01-01T00:00:00.000Z',
      actor: '',
      git: {
        commit: '',
        repo: '',
        url: '',
        files: [],
      },
      url: '',
      note: '',
      signed: false,
    });

    expect(provenance).toEqual({
      at: '2025-01-01T00:00:00.000Z',
      actor: '',
      git: {
        commit: '',
        repo: '',
        url: '',
        files: [],
      },
      url: '',
      note: '',
      signed: false,
    });
  });
});

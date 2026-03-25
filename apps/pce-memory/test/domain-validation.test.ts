/**
 * domain/validation.ts のテスト
 * 純粋バリデーション関数のカバレッジ
 */
import { describe, it, expect } from 'vitest';
import * as E from 'fp-ts/Either';
import {
  validateString,
  validateArray,
  validateScope,
  validateScopes,
  validateContentHash,
  validateBoundaryClass,
} from '../src/domain/validation';

describe('validateString', () => {
  it('returns Right for valid string', () => {
    const result = validateString('name', 'hello', 100);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe('hello');
    }
  });

  it('returns Left when value is not a string', () => {
    const result = validateString('name', 42, 100);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('VALIDATION_ERROR');
      expect(result.left.message).toBe('name must be a string');
    }
  });

  it('returns Left for empty string', () => {
    const result = validateString('name', '', 100);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('name cannot be empty');
    }
  });

  it('returns Left when string exceeds maxLength', () => {
    const result = validateString('name', 'abcdef', 3);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('name exceeds maximum length of 3');
    }
  });

  it('allows string at exact maxLength', () => {
    const result = validateString('name', 'abc', 3);
    expect(E.isRight(result)).toBe(true);
  });

  it('returns Left for null', () => {
    const result = validateString('name', null, 100);
    expect(E.isLeft(result)).toBe(true);
  });

  it('returns Left for undefined', () => {
    const result = validateString('name', undefined, 100);
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('validateArray', () => {
  it('returns Right for valid array', () => {
    const result = validateArray<number>('items', [1, 2, 3]);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual([1, 2, 3]);
    }
  });

  it('returns Left when value is not an array', () => {
    const result = validateArray('items', 'not-array');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe('VALIDATION_ERROR');
      expect(result.left.message).toBe('items must be an array');
    }
  });

  it('returns Left when itemValidator fails', () => {
    const result = validateArray<string>('items', [1, 'two', 3], (item) => typeof item === 'string');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('items contains invalid items');
    }
  });

  it('returns Right when all items pass itemValidator', () => {
    const result = validateArray<string>('items', ['a', 'b'], (item) => typeof item === 'string');
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual(['a', 'b']);
    }
  });

  it('returns Right for empty array', () => {
    const result = validateArray('items', []);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual([]);
    }
  });

  it('returns Right for empty array with itemValidator', () => {
    const result = validateArray('items', [], () => false);
    expect(E.isRight(result)).toBe(true);
  });
});

describe('validateScope', () => {
  it.each(['session', 'project', 'principle'] as const)('accepts valid scope: %s', (scope) => {
    const result = validateScope(scope);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe(scope);
    }
  });

  it('rejects invalid scope string', () => {
    const result = validateScope('invalid');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('invalid scope: invalid');
    }
  });

  it('rejects non-string value', () => {
    const result = validateScope(123);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('scope must be a string');
    }
  });
});

describe('validateScopes', () => {
  it('accepts valid scope array', () => {
    const result = validateScopes(['session', 'project']);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual(['session', 'project']);
    }
  });

  it('rejects non-array', () => {
    const result = validateScopes('session');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('scope must be an array');
    }
  });

  it('rejects array with invalid scope', () => {
    const result = validateScopes(['session', 'bad']);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('invalid scope: bad');
    }
  });

  it('rejects array with non-string items', () => {
    const result = validateScopes([123]);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('scope contains invalid items');
    }
  });

  it('accepts empty array', () => {
    const result = validateScopes([]);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toEqual([]);
    }
  });
});

describe('validateContentHash', () => {
  it('accepts valid sha256 hash', () => {
    const hash = `sha256:${'a'.repeat(64)}`;
    const result = validateContentHash(hash);
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe(hash);
    }
  });

  it('rejects hash with wrong prefix', () => {
    const result = validateContentHash(`md5:${'a'.repeat(64)}`);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toContain('content_hash must match pattern');
    }
  });

  it('rejects hash with wrong length hex', () => {
    const result = validateContentHash('sha256:abc');
    expect(E.isLeft(result)).toBe(true);
  });

  it('rejects hash with uppercase hex', () => {
    const result = validateContentHash(`sha256:${'A'.repeat(64)}`);
    expect(E.isLeft(result)).toBe(true);
  });

  it('rejects non-string', () => {
    const result = validateContentHash(42);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('content_hash must be a string');
    }
  });

  it('rejects empty string', () => {
    const result = validateContentHash('');
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('validateBoundaryClass', () => {
  it.each(['public', 'internal', 'pii', 'secret'] as const)(
    'accepts valid boundary_class: %s',
    (bc) => {
      const result = validateBoundaryClass(bc);
      expect(E.isRight(result)).toBe(true);
      if (E.isRight(result)) {
        expect(result.right).toBe(bc);
      }
    }
  );

  it('rejects invalid boundary_class string', () => {
    const result = validateBoundaryClass('confidential');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('invalid boundary_class: confidential');
    }
  });

  it('rejects non-string value', () => {
    const result = validateBoundaryClass(null);
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.message).toBe('boundary_class must be a string');
    }
  });
});

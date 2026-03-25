/**
 * pce-embeddings/redact.ts のテスト
 * Redact処理とprepareForEmbeddingのカバレッジ
 */
import { describe, it, expect } from 'vitest';
import * as E from 'fp-ts/Either';
import { prepareForEmbedding, requiresRedact, redactError, isRedactError } from '../src/redact';

describe('prepareForEmbedding', () => {
  it('passes through public text without redaction', () => {
    const result = prepareForEmbedding('hello world', 'public');
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.text).toBe('hello world');
      expect(result.right.originalText).toBe('hello world');
      expect(result.right.wasRedacted).toBe(false);
      expect(result.right.hash).toMatch(/^[0-9a-f]+$/);
    }
  });

  it('passes through internal text without redaction', () => {
    const result = prepareForEmbedding('internal data', 'internal');
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.wasRedacted).toBe(false);
    }
  });

  it('applies redaction for confidential text', () => {
    const text = 'Contact user@example.com for details';
    const result = prepareForEmbedding(text, 'confidential');
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.originalText).toBe(text);
      expect(result.right.hash).toMatch(/^[0-9a-f]+$/);
    }
  });

  it('redacts email addresses in confidential text', () => {
    const text = 'Send to test@example.com please';
    const result = prepareForEmbedding(text, 'confidential');
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.text).not.toContain('test@example.com');
    }
  });
});

describe('requiresRedact', () => {
  it('returns true for confidential', () => {
    expect(requiresRedact('confidential')).toBe(true);
  });

  it('returns false for public', () => {
    expect(requiresRedact('public')).toBe(false);
  });

  it('returns false for internal', () => {
    expect(requiresRedact('internal')).toBe(false);
  });
});

describe('redactError', () => {
  it('creates RedactError with message', () => {
    const err = redactError('failed');
    expect(err._tag).toBe('RedactError');
    expect(err.message).toBe('failed');
    expect(err.cause).toBeUndefined();
  });

  it('creates RedactError with cause', () => {
    const cause = new Error('original');
    const err = redactError('failed', cause);
    expect(err.cause).toBe(cause);
  });
});

describe('isRedactError', () => {
  it('returns true for RedactError', () => {
    expect(isRedactError(redactError('test'))).toBe(true);
  });

  it('returns false for non-errors', () => {
    expect(isRedactError(null)).toBe(false);
    expect(isRedactError({ _tag: 'Other' })).toBe(false);
    expect(isRedactError('string')).toBe(false);
  });
});

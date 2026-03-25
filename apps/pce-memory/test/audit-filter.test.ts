/**
 * audit/filter.ts のテスト
 * 機密データフィルタリング関数のカバレッジ
 */
import { describe, it, expect } from 'vitest';
import {
  redactSensitiveFields,
  computeDigest,
  sanitizeForAudit,
  sanitizeErrorMessage,
} from '../src/audit/filter';

describe('redactSensitiveFields', () => {
  it('redacts email field', () => {
    const result = redactSensitiveFields({ email: 'user@example.com', name: 'John' });
    expect(result).toEqual({ email: '[REDACTED]', name: 'John' });
  });

  it('redacts nested sensitive fields', () => {
    const result = redactSensitiveFields({
      user: { password: 'secret123', name: 'Alice' },
    });
    expect(result).toEqual({
      user: { password: '[REDACTED]', name: 'Alice' },
    });
  });

  it('redacts all known sensitive field patterns', () => {
    const input = {
      email: 'x',
      phone: 'x',
      password: 'x',
      secret: 'x',
      token: 'x',
      authorization: 'x',
      api_key: 'x',
      apikey: 'x',
      credential: 'x',
      private_key: 'x',
      privatekey: 'x',
      safe_field: 'visible',
    };
    const result = redactSensitiveFields(input);
    expect(result.safe_field).toBe('visible');
    expect(result.email).toBe('[REDACTED]');
    expect(result.phone).toBe('[REDACTED]');
    expect(result.password).toBe('[REDACTED]');
    expect(result.secret).toBe('[REDACTED]');
    expect(result.token).toBe('[REDACTED]');
    expect(result.authorization).toBe('[REDACTED]');
    expect(result.api_key).toBe('[REDACTED]');
    expect(result.apikey).toBe('[REDACTED]');
    expect(result.credential).toBe('[REDACTED]');
    expect(result.private_key).toBe('[REDACTED]');
    expect(result.privatekey).toBe('[REDACTED]');
  });

  it('is case-insensitive for field names', () => {
    const result = redactSensitiveFields({ EMAIL: 'test', Password: 'x' });
    expect(result.EMAIL).toBe('[REDACTED]');
    expect(result.Password).toBe('[REDACTED]');
  });

  it('handles arrays', () => {
    const result = redactSensitiveFields([{ token: 'abc' }, { name: 'ok' }]);
    expect(result).toEqual([{ token: '[REDACTED]' }, { name: 'ok' }]);
  });

  it('returns null as-is', () => {
    expect(redactSensitiveFields(null)).toBeNull();
  });

  it('returns undefined as-is', () => {
    expect(redactSensitiveFields(undefined)).toBeUndefined();
  });

  it('returns primitives as-is', () => {
    expect(redactSensitiveFields('hello')).toBe('hello');
    expect(redactSensitiveFields(42)).toBe(42);
    expect(redactSensitiveFields(true)).toBe(true);
  });

  it('handles deeply nested objects', () => {
    const result = redactSensitiveFields({
      level1: { level2: { api_key: 'deep_secret', data: 'ok' } },
    });
    expect(result).toEqual({
      level1: { level2: { api_key: '[REDACTED]', data: 'ok' } },
    });
  });
});

describe('computeDigest', () => {
  it('returns sha256: prefixed hex digest', () => {
    const result = computeDigest('hello');
    expect(result).toMatch(/^sha256:[0-9a-f]{64}$/);
  });

  it('is deterministic', () => {
    expect(computeDigest('test')).toBe(computeDigest('test'));
  });

  it('produces different digests for different inputs', () => {
    expect(computeDigest('a')).not.toBe(computeDigest('b'));
  });
});

describe('sanitizeForAudit', () => {
  it('returns digest and length', () => {
    const result = sanitizeForAudit('hello world');
    expect(result.payload_digest).toMatch(/^sha256:[0-9a-f]{64}$/);
    expect(result.payload_length).toBe(11);
    expect(result.metadata).toBeUndefined();
  });

  it('redacts sensitive fields in metadata', () => {
    const result = sanitizeForAudit('payload', { token: 'secret', user: 'alice' });
    expect(result.metadata).toEqual({ token: '[REDACTED]', user: 'alice' });
  });

  it('handles metadata without sensitive fields', () => {
    const result = sanitizeForAudit('payload', { action: 'read' });
    expect(result.metadata).toEqual({ action: 'read' });
  });
});

describe('sanitizeErrorMessage', () => {
  it('extracts message from Error and redacts paths', () => {
    const err = new Error('Failed to read /home/user/secret/file.txt');
    const result = sanitizeErrorMessage(err);
    expect(result).toBe('Failed to read [PATH]');
    expect(result).not.toContain('/home');
  });

  it('returns string representation for non-Error', () => {
    expect(sanitizeErrorMessage('simple error')).toBe('simple error');
    expect(sanitizeErrorMessage(42)).toBe('42');
    expect(sanitizeErrorMessage(null)).toBe('null');
  });

  it('handles Error without path info', () => {
    const err = new Error('Something went wrong');
    expect(sanitizeErrorMessage(err)).toBe('Something went wrong');
  });

  it('redacts multiple paths', () => {
    const err = new Error('Cannot read /a/b and write /c/d');
    const result = sanitizeErrorMessage(err);
    expect(result).toBe('Cannot read [PATH] and write [PATH]');
  });
});

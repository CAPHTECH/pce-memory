/**
 * マージ戦略テスト (Issue #18)
 */
import { describe, it, expect } from 'vitest';
import {
  mergeBoundaryClass,
  isBoundarySyncable,
  isBoundaryUpgraded,
  BOUNDARY_STRICTNESS,
} from '../src/sync/merge.js';

describe('BOUNDARY_STRICTNESS', () => {
  it('public < internal < pii < secret の順序', () => {
    expect(BOUNDARY_STRICTNESS['public']).toBeLessThan(BOUNDARY_STRICTNESS['internal']);
    expect(BOUNDARY_STRICTNESS['internal']).toBeLessThan(BOUNDARY_STRICTNESS['pii']);
    expect(BOUNDARY_STRICTNESS['pii']).toBeLessThan(BOUNDARY_STRICTNESS['secret']);
  });
});

describe('mergeBoundaryClass', () => {
  it('同じboundary_classの場合はそのまま返す', () => {
    expect(mergeBoundaryClass('public', 'public')).toBe('public');
    expect(mergeBoundaryClass('internal', 'internal')).toBe('internal');
    expect(mergeBoundaryClass('pii', 'pii')).toBe('pii');
    expect(mergeBoundaryClass('secret', 'secret')).toBe('secret');
  });

  it('incomingがより厳格な場合はincomingを返す（格上げ）', () => {
    expect(mergeBoundaryClass('public', 'internal')).toBe('internal');
    expect(mergeBoundaryClass('public', 'pii')).toBe('pii');
    expect(mergeBoundaryClass('public', 'secret')).toBe('secret');
    expect(mergeBoundaryClass('internal', 'pii')).toBe('pii');
    expect(mergeBoundaryClass('internal', 'secret')).toBe('secret');
    expect(mergeBoundaryClass('pii', 'secret')).toBe('secret');
  });

  it('existingがより厳格な場合はexistingを返す（格下げ防止）', () => {
    expect(mergeBoundaryClass('internal', 'public')).toBe('internal');
    expect(mergeBoundaryClass('pii', 'public')).toBe('pii');
    expect(mergeBoundaryClass('secret', 'public')).toBe('secret');
    expect(mergeBoundaryClass('pii', 'internal')).toBe('pii');
    expect(mergeBoundaryClass('secret', 'internal')).toBe('secret');
    expect(mergeBoundaryClass('secret', 'pii')).toBe('secret');
  });
});

describe('isBoundarySyncable', () => {
  it('secretは常にfalseを返す', () => {
    expect(isBoundarySyncable('secret', ['public', 'internal', 'pii', 'secret'])).toBe(false);
    expect(isBoundarySyncable('secret', ['secret'])).toBe(false);
  });

  it('allowedClassesに含まれる場合はtrue', () => {
    expect(isBoundarySyncable('public', ['public'])).toBe(true);
    expect(isBoundarySyncable('internal', ['public', 'internal'])).toBe(true);
    expect(isBoundarySyncable('pii', ['public', 'internal', 'pii'])).toBe(true);
  });

  it('allowedClassesに含まれない場合はfalse', () => {
    expect(isBoundarySyncable('public', ['internal'])).toBe(false);
    expect(isBoundarySyncable('pii', ['public', 'internal'])).toBe(false);
  });
});

describe('isBoundaryUpgraded', () => {
  it('afterがbeforeより厳格な場合はtrue', () => {
    expect(isBoundaryUpgraded('public', 'internal')).toBe(true);
    expect(isBoundaryUpgraded('public', 'pii')).toBe(true);
    expect(isBoundaryUpgraded('internal', 'secret')).toBe(true);
  });

  it('同じ場合はfalse', () => {
    expect(isBoundaryUpgraded('public', 'public')).toBe(false);
    expect(isBoundaryUpgraded('internal', 'internal')).toBe(false);
  });

  it('afterがbeforeより緩い場合はfalse', () => {
    expect(isBoundaryUpgraded('internal', 'public')).toBe(false);
    expect(isBoundaryUpgraded('secret', 'pii')).toBe(false);
  });
});

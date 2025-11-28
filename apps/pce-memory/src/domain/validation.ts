/**
 * バリデーション関数
 * V1 Conservative設計: 純粋関数でEither<DomainError, T>を返す
 */
import * as E from 'fp-ts/Either';
import { pipe } from 'fp-ts/function';
import type { DomainError } from './errors.js';
import { validationError } from './errors.js';

// 文字列バリデーション
export const validateString = (
  field: string,
  value: unknown,
  maxLength: number
): E.Either<DomainError, string> => {
  if (typeof value !== 'string') {
    return E.left(validationError(`${field} must be a string`));
  }
  if (value.length === 0) {
    return E.left(validationError(`${field} cannot be empty`));
  }
  if (value.length > maxLength) {
    return E.left(validationError(`${field} exceeds maximum length of ${maxLength}`));
  }
  return E.right(value);
};

// 配列バリデーション
export const validateArray = <T>(
  field: string,
  value: unknown,
  itemValidator?: (item: unknown) => boolean
): E.Either<DomainError, T[]> => {
  if (!Array.isArray(value)) {
    return E.left(validationError(`${field} must be an array`));
  }
  if (itemValidator && !value.every(itemValidator)) {
    return E.left(validationError(`${field} contains invalid items`));
  }
  return E.right(value as T[]);
};

// スコープバリデーション
const VALID_SCOPES = ['session', 'project', 'principle'] as const;
export type ValidScope = (typeof VALID_SCOPES)[number];

export const validateScope = (scope: unknown): E.Either<DomainError, ValidScope> => {
  if (typeof scope !== 'string') {
    return E.left(validationError('scope must be a string'));
  }
  if (!VALID_SCOPES.includes(scope as ValidScope)) {
    return E.left(validationError(`invalid scope: ${scope}`));
  }
  return E.right(scope as ValidScope);
};

// スコープ配列バリデーション
export const validateScopes = (scopes: unknown): E.Either<DomainError, ValidScope[]> => {
  return pipe(
    validateArray<string>('scope', scopes, (s) => typeof s === 'string'),
    E.chain((arr) => {
      const invalid = arr.find((s) => !VALID_SCOPES.includes(s as ValidScope));
      if (invalid) {
        return E.left(validationError(`invalid scope: ${invalid}`));
      }
      return E.right(arr as ValidScope[]);
    })
  );
};

// コンテンツハッシュバリデーション
const CONTENT_HASH_PATTERN = /^sha256:[0-9a-f]{64}$/;

export const validateContentHash = (hash: unknown): E.Either<DomainError, string> => {
  return pipe(
    validateString('content_hash', hash, 80),
    E.chain((s) =>
      CONTENT_HASH_PATTERN.test(s)
        ? E.right(s)
        : E.left(validationError('content_hash must match pattern sha256:[64 hex chars]'))
    )
  );
};

// boundary_classバリデーション
const VALID_BOUNDARY_CLASSES = ['public', 'internal', 'pii', 'secret'] as const;
export type ValidBoundaryClass = (typeof VALID_BOUNDARY_CLASSES)[number];

export const validateBoundaryClass = (bc: unknown): E.Either<DomainError, ValidBoundaryClass> => {
  if (typeof bc !== 'string') {
    return E.left(validationError('boundary_class must be a string'));
  }
  if (!VALID_BOUNDARY_CLASSES.includes(bc as ValidBoundaryClass)) {
    return E.left(validationError(`invalid boundary_class: ${bc}`));
  }
  return E.right(bc as ValidBoundaryClass);
};

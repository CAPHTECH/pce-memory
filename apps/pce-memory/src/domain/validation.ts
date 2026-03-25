/**
 * バリデーション関数
 * V1 Conservative設計: 純粋関数でEither<DomainError, T>を返す
 */
import * as E from 'fp-ts/Either';
import type { DomainError } from './errors.js';
import { validationError, embeddingValidationError } from './errors.js';

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

// 複数フィールドの一括バリデーション
export const validateStringFields = (
  fields: ReadonlyArray<readonly [field: string, value: unknown, maxLength: number]>
): E.Either<DomainError, void> => {
  for (const [field, value, maxLength] of fields) {
    const result = validateString(field, value, maxLength);
    if (E.isLeft(result)) return result;
  }
  return E.right(undefined);
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
  if (itemValidator && value.length > 0) {
    const allValid = value.every(itemValidator);
    if (!allValid) {
      return E.left(validationError(`${field} contains invalid items`));
    }
  }
  return E.right(value as T[]);
};

// スコープバリデーション
const VALID_SCOPES = ['session', 'project', 'principle'] as const;

export const validateScope = (value: unknown): E.Either<DomainError, string> => {
  if (typeof value !== 'string') {
    return E.left(validationError('scope must be a string'));
  }
  if (!(VALID_SCOPES as readonly string[]).includes(value)) {
    return E.left(validationError(`invalid scope: ${value}`));
  }
  return E.right(value);
};

export const validateScopes = (value: unknown): E.Either<DomainError, string[]> => {
  if (!Array.isArray(value)) {
    return E.left(validationError('scope must be an array'));
  }
  for (const item of value) {
    if (typeof item !== 'string') {
      return E.left(validationError('scope contains invalid items'));
    }
    if (!(VALID_SCOPES as readonly string[]).includes(item)) {
      return E.left(validationError(`invalid scope: ${item}`));
    }
  }
  return E.right(value as string[]);
};

// content_hashバリデーション
const CONTENT_HASH_PATTERN = /^sha256:[a-f0-9]{64}$/;

export const validateContentHash = (value: unknown): E.Either<DomainError, string> => {
  if (typeof value !== 'string') {
    return E.left(validationError('content_hash must be a string'));
  }
  if (!CONTENT_HASH_PATTERN.test(value)) {
    return E.left(validationError('content_hash must match pattern sha256:<64 hex chars>'));
  }
  return E.right(value);
};

// boundary_classバリデーション
const VALID_BOUNDARY_CLASSES = ['public', 'internal', 'pii', 'secret'] as const;

export const validateBoundaryClass = (value: unknown): E.Either<DomainError, string> => {
  if (typeof value !== 'string') {
    return E.left(validationError('boundary_class must be a string'));
  }
  if (!(VALID_BOUNDARY_CLASSES as readonly string[]).includes(value)) {
    return E.left(validationError(`invalid boundary_class: ${value}`));
  }
  return E.right(value);
};

// 埋め込みベクトルバリデーション
const MAX_EMBEDDING_DIM = 4096;
const MAX_EMBEDDING_MAGNITUDE = 10.0;

export const validateEmbedding = (embedding: readonly number[]): E.Either<DomainError, void> => {
  if (embedding.length === 0) {
    return E.left(embeddingValidationError('Embedding vector must not be empty'));
  }
  if (embedding.length > MAX_EMBEDDING_DIM) {
    return E.left(
      embeddingValidationError(
        `Embedding dimension ${embedding.length} exceeds maximum ${MAX_EMBEDDING_DIM}`
      )
    );
  }
  for (let i = 0; i < embedding.length; i++) {
    const v = embedding[i];
    if (typeof v !== 'number' || !Number.isFinite(v)) {
      return E.left(embeddingValidationError(`Invalid embedding value at index ${i}: ${v}`));
    }
    if (Math.abs(v) > MAX_EMBEDDING_MAGNITUDE) {
      return E.left(
        embeddingValidationError(
          `Embedding value ${v} at index ${i} exceeds magnitude limit ${MAX_EMBEDDING_MAGNITUDE}`
        )
      );
    }
  }
  return E.right(undefined);
};

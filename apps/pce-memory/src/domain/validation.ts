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

// 埋め込みベクトルバリデーション
const MAX_EMBEDDING_DIM = 4096;
const MAX_EMBEDDING_MAGNITUDE = 10.0;

export const validateEmbedding = (
  embedding: readonly number[]
): E.Either<DomainError, void> => {
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

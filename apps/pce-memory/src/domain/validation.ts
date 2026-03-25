/**
 * Validation functions for domain types.
 *
 * Restored: validateEmbedding was removed in dead-code cleanup but is still
 * imported by hybridSearch.ts.
 */
import * as E from 'fp-ts/Either';
import type { DomainError } from './errors.js';
import { embeddingValidationError } from './errors.js';

const MAX_EMBEDDING_DIM = 4096;
const MAX_EMBEDDING_MAGNITUDE = 10.0;

export const validateEmbedding = (
  embedding: readonly number[],
): E.Either<DomainError, void> => {
  if (embedding.length === 0) {
    return E.left(embeddingValidationError('Embedding vector must not be empty'));
  }
  if (embedding.length > MAX_EMBEDDING_DIM) {
    return E.left(
      embeddingValidationError(
        `Embedding dimension ${embedding.length} exceeds maximum ${MAX_EMBEDDING_DIM}`,
      ),
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
          `Embedding value ${v} at index ${i} exceeds magnitude limit ${MAX_EMBEDDING_MAGNITUDE}`,
        ),
      );
    }
  }
  return E.right(undefined);
};

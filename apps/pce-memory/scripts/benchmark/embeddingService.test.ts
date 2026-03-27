import { afterEach, describe, expect, it } from 'vitest';
import * as E from 'fp-ts/Either';
import type { EmbeddingService } from '@pce/embeddings';
import { getEmbeddingService, setEmbeddingService } from '../../src/store/hybridSearch.js';
import {
  createBenchmarkEmbeddingService,
  withRestoredEmbeddingService,
} from './embeddingService.js';

afterEach(() => {
  setEmbeddingService(null as unknown as EmbeddingService);
});

describe('benchmark embedding service helpers', () => {
  it('implements the full EmbeddingService contract needed by benchmark scripts', async () => {
    const service = createBenchmarkEmbeddingService(
      {
        alpha: [1, 0],
        beta: [0, 1],
      },
      {
        fallbackEmbedding: [-1, 0],
        modelVersion: 'benchmark-contract-v1',
      }
    );

    expect(service.modelVersion).toBe('benchmark-contract-v1');
    expect(service.primaryStatus).toBe('available');

    const singleResult = await service.embed({ text: 'alpha', sensitivity: 'internal' })();
    expect(E.isRight(singleResult)).toBe(true);
    if (E.isRight(singleResult)) {
      expect(singleResult.right.embedding).toEqual([1, 0]);
      expect(singleResult.right.modelVersion).toBe('benchmark-contract-v1');
      expect(singleResult.right.fromCache).toBe(false);
      expect(singleResult.right.textHash).toBeTruthy();
    }

    const batchResult = await service.embedBatch([
      { text: 'alpha', sensitivity: 'internal' },
      { text: 'missing', sensitivity: 'internal' },
    ])();
    expect(E.isRight(batchResult)).toBe(true);
    if (E.isRight(batchResult)) {
      expect(batchResult.right.processedCount).toBe(2);
      expect(batchResult.right.cacheHits).toBe(0);
      expect(batchResult.right.results.map((result) => result.embedding)).toEqual([
        [1, 0],
        [-1, 0],
      ]);
    }

    const clearResult = await service.clearCache()();
    expect(E.isRight(clearResult)).toBe(true);

    const updateResult = await service.updateModelVersion('benchmark-contract-v2')();
    expect(E.isRight(updateResult)).toBe(true);
    expect(service.modelVersion).toBe('benchmark-contract-v2');
  });

  it('restores the previous global embedding service after a benchmark run', async () => {
    const sentinel = createBenchmarkEmbeddingService(
      { sentinel: [0.5, 0.5] },
      { modelVersion: 'sentinel-v1' }
    );
    setEmbeddingService(sentinel);

    await withRestoredEmbeddingService(async () => {
      setEmbeddingService(
        createBenchmarkEmbeddingService({ benchmark: [1, 0] }, { modelVersion: 'benchmark-v1' })
      );
    });

    expect(getEmbeddingService()).toBe(sentinel);
  });
});

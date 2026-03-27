import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { getEmbeddingService, setEmbeddingService } from '../../src/store/hybridSearch.js';

interface CreateBenchmarkEmbeddingServiceOptions {
  fallbackEmbedding?: readonly number[];
  modelVersion?: string;
}

function buildEmbedResult(
  text: string,
  embedding: readonly number[],
  modelVersion: string
): {
  embedding: readonly number[];
  modelVersion: string;
  fromCache: false;
  textHash: string;
} {
  return {
    embedding,
    modelVersion,
    fromCache: false,
    textHash: computeContentHash(text),
  };
}

export function createBenchmarkEmbeddingService(
  embeddings: Record<string, readonly number[]>,
  options: CreateBenchmarkEmbeddingServiceOptions = {}
): EmbeddingService {
  let currentModelVersion = options.modelVersion ?? 'benchmark-v1';
  const fallbackEmbedding = options.fallbackEmbedding ?? [1, 0];

  const resolveEmbedding = (text: string): readonly number[] =>
    embeddings[text] ?? fallbackEmbedding;

  return {
    get modelVersion() {
      return currentModelVersion;
    },
    get primaryStatus() {
      return 'available';
    },
    embed:
      ({ text }) =>
      async () =>
        E.right(buildEmbedResult(text, resolveEmbedding(text), currentModelVersion)),
    embedBatch: (params) => async () =>
      E.right({
        results: params.map(({ text }) =>
          buildEmbedResult(text, resolveEmbedding(text), currentModelVersion)
        ),
        processedCount: params.length,
        cacheHits: 0,
      }),
    clearCache: () => async () => E.right(undefined),
    updateModelVersion: (newVersion) => async () => {
      currentModelVersion = newVersion;
      return E.right(undefined);
    },
  };
}

export async function withRestoredEmbeddingService<T>(run: () => Promise<T>): Promise<T> {
  const previous = getEmbeddingService();
  try {
    return await run();
  } finally {
    setEmbeddingService(previous);
  }
}

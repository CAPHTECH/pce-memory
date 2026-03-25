/**
 * Latency profiling: cold-start, embedding, search, rerank overhead.
 */

import { performance } from 'node:perf_hooks';
import { TEST_CLAIMS } from '../../assay/test-data.ts';
import { initDb, initSchema, resetDbAsync } from '../../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../../src/store/hybridSearch';
import {
  initLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';
import type { EmbeddingService } from '@pce/embeddings';
import type { ClaimKind } from '../../../src/domain/types';
import { computeLatencyStats, type LatencyProfileResult } from '../types';

const SEARCH_REPS = 20;
const REPRESENTATIVE_QUERY = 'JWT認証 アクセストークン';

async function warmup(embeddingService: EmbeddingService): Promise<void> {
  for (const claim of TEST_CLAIMS) {
    await upsertClaimWithEmbedding(
      {
        text: claim.text,
        kind: claim.kind as ClaimKind,
        scope: claim.scope as 'session' | 'project' | 'principle',
        boundary_class: claim.boundary_class as 'public' | 'internal' | 'pii' | 'secret',
        content_hash: claim.content_hash,
        provenance: claim.provenance,
      },
      embeddingService
    );
  }
}

async function measureColdStart(): Promise<{
  coldStartMs: number;
  embeddingService: EmbeddingService;
}> {
  const t0 = performance.now();
  await initLocalProvider();
  const coldStartMs = performance.now() - t0;

  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  const embeddingService = createLocalOnlyService(localProvider, cache);
  return { coldStartMs, embeddingService };
}

async function measureEmbeddingLatency(
  embeddingService: EmbeddingService
): Promise<{ coldMs: number; warmMs: number }> {
  const text = 'ベンチマーク用テスト文字列: ハイブリッド検索の性能評価';

  // Cold (first call, no cache)
  const t0 = performance.now();
  await embeddingService.embed({ text, sensitivity: 'public' })();
  const coldMs = performance.now() - t0;

  // Warm (cached)
  const t1 = performance.now();
  await embeddingService.embed({ text, sensitivity: 'public' })();
  const warmMs = performance.now() - t1;

  return { coldMs, warmMs };
}

async function measureSearchLatency(
  embeddingService: EmbeddingService,
  enableRerank: boolean
): Promise<number[]> {
  const latencies: number[] = [];
  for (let i = 0; i < SEARCH_REPS; i++) {
    const t0 = performance.now();
    await hybridSearchPaginated(['session', 'project', 'principle'], 10, REPRESENTATIVE_QUERY, {
      embeddingService,
      alpha: 0.65,
      enableRerank,
    });
    latencies.push(performance.now() - t0);
  }
  return latencies;
}

export async function runLatencyProfile(): Promise<{
  result: LatencyProfileResult;
  embeddingService: EmbeddingService;
}> {
  console.log('  [latency] Measuring cold start...');
  const { coldStartMs, embeddingService } = await measureColdStart();
  console.log(`    Cold start: ${coldStartMs.toFixed(0)}ms`);

  console.log('  [latency] Measuring embedding latency...');
  const embedding = await measureEmbeddingLatency(embeddingService);
  console.log(
    `    Embedding cold=${embedding.coldMs.toFixed(1)}ms warm=${embedding.warmMs.toFixed(1)}ms`
  );

  // Setup DB for search measurements
  process.env.PCE_DB = ':memory:';
  await resetDbAsync();
  await initDb();
  await initSchema();
  setEmbeddingService(embeddingService);
  await warmup(embeddingService);

  console.log(`  [latency] Measuring search latency (${SEARCH_REPS} reps)...`);
  const withRerank = await measureSearchLatency(embeddingService, true);
  const withoutRerank = await measureSearchLatency(embeddingService, false);

  const withRerankStats = computeLatencyStats(withRerank);
  const withoutRerankStats = computeLatencyStats(withoutRerank);

  console.log(`    Search with rerank p50=${withRerankStats.p50.toFixed(1)}ms`);
  console.log(`    Search without rerank p50=${withoutRerankStats.p50.toFixed(1)}ms`);

  return {
    result: {
      coldStartMs,
      embedding,
      search: withRerankStats,
      rerankOverhead: {
        withRerank: withRerankStats,
        withoutRerank: withoutRerankStats,
        overheadMs: withRerankStats.mean - withoutRerankStats.mean,
      },
    },
    embeddingService,
  };
}

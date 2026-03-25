/**
 * Diagnostic: Hypothesis 3 - kVec/kText Sensitivity
 *
 * Tests whether varying k values improves recall at larger corpus sizes.
 *
 * Run: npx tsx apps/pce-memory/scripts/benchmark/diagnostics/k-sensitivity.ts
 */

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from 'yaml';
import {
  initLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';
import { evaluateRetrieval } from '../../../external/assay-kit/packages/assay-kit/src/metrics/combined.ts';
import { initDb, initSchema, resetDbAsync } from '../../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
// Note: EmbeddingService type still needed for seedClaims param
import type { ClaimKind } from '../../../src/domain/types';
import { generateClaims, type SyntheticClaim } from '../data/synthetic-claims';

type Query = {
  id: string;
  text: string;
  metadata?: { expected?: Array<string | { path: string; relevance: number }> };
};

async function seedClaims(
  claims: SyntheticClaim[],
  embeddingService: EmbeddingService
): Promise<Map<string, string>> {
  const idMap = new Map<string, string>();
  for (const claim of claims) {
    const result = await upsertClaimWithEmbedding(
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
    idMap.set(claim.id, result.claim.id);
  }
  return idMap;
}

async function main() {
  console.log('=== Hypothesis 3: kVec/kText Sensitivity ===\n');

  await initLocalProvider();
  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  const embeddingService = createLocalOnlyService(localProvider, cache);
  const repoRoot = join(import.meta.dirname, '../../..');
  const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const raw = readFileSync(datasetPath, 'utf-8');
  const dataset = parse(raw) as { queries: Query[] };
  const queries = dataset.queries;

  const kVecValues = [48, 96, 192, 384];
  const kTextValues = [24, 48, 96, 192];
  const scalePoints = [100, 500, 1000];

  for (const scalePoint of scalePoints) {
    console.log(`\n--- Scale: ${scalePoint} claims ---`);

    process.env.PCE_DB = ':memory:';
    await resetDbAsync();
    await initDb();
    await initSchema();
    setEmbeddingService(embeddingService);

    const claims = generateClaims(scalePoint);
    const idMap = await seedClaims(claims, embeddingService);

    console.log(`\n  Recall@10 matrix (kText \\ kVec):`);
    console.log(
      `  ${'kText\\kVec'.padEnd(10)} | ${kVecValues.map((v) => String(v).padStart(6)).join(' | ')}`
    );
    console.log(`  ${'-'.repeat(10)} | ${kVecValues.map(() => '------').join(' | ')}`);

    for (const kText of kTextValues) {
      const recalls: number[] = [];

      for (const kVec of kVecValues) {
        const allRecalls: number[] = [];

        for (const query of queries) {
          const searchResult = await hybridSearchPaginated(
            ['session', 'project', 'principle'],
            10,
            query.text,
            { embeddingService, alpha: 0.65, enableRerank: true, kText, kVec }
          );

          const retrievedIds = searchResult.results.map((c) => c.claim.id);
          const relevantIdSet = new Set<string>();
          const relevanceGrades = new Map<string, number>();

          if (Array.isArray(query.metadata?.expected)) {
            for (const item of query.metadata!.expected!) {
              if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
                const cid = idMap.get(item.path);
                if (cid) {
                  relevanceGrades.set(cid, item.relevance);
                  if (item.relevance > 0) relevantIdSet.add(cid);
                }
              } else if (typeof item === 'string') {
                const cid = idMap.get(item);
                if (cid) {
                  relevanceGrades.set(cid, 1);
                  relevantIdSet.add(cid);
                }
              }
            }
          }

          const evalStartTime = Date.now();
          const metrics = evaluateRetrieval({
            items: retrievedIds.map((id, i) => ({ id, timestampMs: evalStartTime + i * 10 })),
            relevant: Array.from(relevantIdSet),
            k: 10,
            startTimestampMs: evalStartTime,
            ...(relevanceGrades.size > 0 ? { relevanceGrades } : {}),
          });

          allRecalls.push(metrics.recallAtK);
        }

        const avgRecall = allRecalls.reduce((a, b) => a + b, 0) / allRecalls.length;
        recalls.push(avgRecall);
      }

      console.log(
        `  ${String(kText).padEnd(10)} | ${recalls.map((r) => `${(r * 100).toFixed(1)}%`.padStart(6)).join(' | ')}`
      );
    }
  }
}

main().catch(console.error);

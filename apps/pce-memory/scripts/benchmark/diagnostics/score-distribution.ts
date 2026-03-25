/**
 * Diagnostic: Score Distribution Analysis
 *
 * Captures full score distributions (text, vec, fused) at each scale point,
 * comparing golden vs synthetic claim scores.
 *
 * Run: npx tsx apps/pce-memory/scripts/benchmark/diagnostics/score-distribution.ts
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
import { initDb, initSchema, resetDbAsync } from '../../../src/db/connection';
import { upsertClaimWithEmbedding } from '../../../src/store/claims';
import { hybridSearchPaginated, setEmbeddingService } from '../../../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
import type { ClaimKind } from '../../../src/domain/types';
import { generateClaims, type SyntheticClaim } from '../data/synthetic-claims';
import { TEST_CLAIMS } from '../../assay/test-data';

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
  console.log('=== Score Distribution Analysis ===\n');

  await initLocalProvider();
  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  const embeddingService = createLocalOnlyService(localProvider, cache);
  const repoRoot = join(import.meta.dirname, '../../..');
  const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const raw = readFileSync(datasetPath, 'utf-8');
  const dataset = parse(raw) as { queries: Query[] };
  const queries = dataset.queries;

  const goldenTestIds = new Set(TEST_CLAIMS.map((c) => c.id));

  for (const scalePoint of [15, 100, 500, 1000]) {
    console.log(`\n--- Scale: ${scalePoint} claims ---`);

    process.env.PCE_DB = ':memory:';
    await resetDbAsync();
    await initDb();
    await initSchema();
    setEmbeddingService(embeddingService);

    const claims = generateClaims(scalePoint);
    const idMap = await seedClaims(claims, embeddingService);

    // Reverse map: claimId -> testId
    const reverseIdMap = new Map<string, string>();
    for (const [testId, claimId] of idMap) {
      reverseIdMap.set(claimId, testId);
    }

    // For a few representative queries, show full score breakdown
    const sampleQueries = queries.slice(0, 5);

    for (const query of sampleQueries) {
      console.log(`\n  Query: "${query.text}" (${query.id})`);

      const searchResult = await hybridSearchPaginated(
        ['session', 'project', 'principle'],
        20, // Get more results to see distribution
        query.text,
        { embeddingService, alpha: 0.65, enableRerank: true, includeBreakdown: true }
      );

      const expectedIds = new Set<string>();
      if (Array.isArray(query.metadata?.expected)) {
        for (const item of query.metadata!.expected!) {
          const path = typeof item === 'object' ? item.path : item;
          const cid = idMap.get(path);
          if (cid) expectedIds.add(cid);
        }
      }

      const goldenScores: number[] = [];
      const synthScores: number[] = [];

      console.log(
        `  ${'Rank'.padStart(4)} | ${'ID'.padEnd(20)} | ${'Score'.padStart(6)} | ${'Type'.padEnd(8)} | Expected`
      );
      console.log(
        `  ${'-'.repeat(4)} | ${'-'.repeat(20)} | ${'-'.repeat(6)} | ${'-'.repeat(8)} | --------`
      );

      for (let i = 0; i < searchResult.results.length; i++) {
        const r = searchResult.results[i]!;
        const testId = reverseIdMap.get(r.claim.id) ?? r.claim.id.slice(0, 20);
        const isGolden = goldenTestIds.has(reverseIdMap.get(r.claim.id) ?? '');
        const isExpected = expectedIds.has(r.claim.id);
        const type = isGolden ? 'golden' : 'synth';

        if (isGolden) goldenScores.push(r.score);
        else synthScores.push(r.score);

        const breakdown = r.score_breakdown;
        const breakdownStr = breakdown
          ? ` (vec=${breakdown.s_vec.toFixed(3)}, text=${breakdown.s_text.toFixed(3)}, g=${breakdown.g.g.toFixed(3)})`
          : '';

        console.log(
          `  ${String(i + 1).padStart(4)} | ${testId.padEnd(20)} | ${r.score.toFixed(4)} | ${type.padEnd(8)} | ${isExpected ? 'YES' : ''}${breakdownStr}`
        );
      }

      // Summary stats
      goldenScores.sort((a, b) => a - b);
      synthScores.sort((a, b) => a - b);

      if (goldenScores.length > 0 && synthScores.length > 0) {
        const goldenMin = goldenScores[0]!;
        const synthMax = synthScores[synthScores.length - 1]!;
        const separation = goldenMin - synthMax;
        console.log(
          `  Separation: golden_min=${goldenMin.toFixed(4)} - synth_max=${synthMax.toFixed(4)} = ${separation.toFixed(4)}`
        );
      }
    }
  }
}

main().catch(console.error);

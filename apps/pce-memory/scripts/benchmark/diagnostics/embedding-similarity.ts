/**
 * Diagnostic: Hypothesis 1 - Synthetic-Golden Cosine Similarity
 *
 * Measures cosine similarity between golden claims and synthetic claims
 * to determine if synthetic noise is too semantically close to golden claims.
 *
 * Run: node_modules/.bin/tsx scripts/benchmark/diagnostics/embedding-similarity.ts
 */

import {
  initLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';
import { generateClaims } from '../data/synthetic-claims';
import { TEST_CLAIMS } from '../../assay/test-data';

function cosineSimilarity(a: readonly number[], b: readonly number[]): number {
  let dot = 0;
  let normA = 0;
  let normB = 0;
  for (let i = 0; i < a.length; i++) {
    dot += a[i]! * b[i]!;
    normA += a[i]! * a[i]!;
    normB += b[i]! * b[i]!;
  }
  const denom = Math.sqrt(normA) * Math.sqrt(normB);
  return denom === 0 ? 0 : dot / denom;
}

function percentile(sorted: number[], p: number): number {
  const idx = Math.min(Math.floor(sorted.length * p), sorted.length - 1);
  return sorted[idx]!;
}

async function embed(
  embeddingService: ReturnType<typeof createLocalOnlyService>,
  text: string
): Promise<readonly number[] | null> {
  const result = await embeddingService.embed({ text, sensitivity: 'internal' })();
  // fp-ts Either: _tag === 'Right' means success
  if (result._tag === 'Right') return result.right.embedding;
  return null;
}

async function main() {
  console.log('=== Hypothesis 1: Embedding Similarity Analysis ===\n');

  await initLocalProvider();
  const cache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
  const embeddingService = createLocalOnlyService(localProvider, cache);
  const goldenIds = new Set(TEST_CLAIMS.map((c) => c.id));

  for (const scalePoint of [100, 500, 1000]) {
    console.log(`\n--- Scale: ${scalePoint} claims ---`);
    const claims = generateClaims(scalePoint);
    const golden = claims.filter((c) => goldenIds.has(c.id));
    const synthetic = claims.filter((c) => !goldenIds.has(c.id));

    if (synthetic.length === 0) {
      console.log('  No synthetic claims at this scale, skipping.');
      continue;
    }

    // Embed all claims
    const goldenEmbeddings = new Map<string, readonly number[]>();
    for (const c of golden) {
      const emb = await embed(embeddingService, c.text);
      if (emb) goldenEmbeddings.set(c.id, emb);
    }

    const syntheticEmbeddings: Array<{ id: string; embedding: readonly number[] }> = [];
    for (const c of synthetic) {
      const emb = await embed(embeddingService, c.text);
      if (emb) syntheticEmbeddings.push({ id: c.id, embedding: emb });
    }

    // For each golden claim, compute similarity to ALL synthetic claims
    console.log(`\n  Golden claim → synthetic similarity distributions:`);
    console.log(`  ${'Claim ID'.padEnd(25)} | Mean   | P50    | P75    | P90    | Max    | >0.7`);
    console.log(`  ${'-'.repeat(25)} | ------ | ------ | ------ | ------ | ------ | ----`);

    const allSimilarities: number[] = [];

    for (const [goldenId, goldenEmb] of goldenEmbeddings) {
      const sims: number[] = [];
      for (const synth of syntheticEmbeddings) {
        const sim = cosineSimilarity(goldenEmb, synth.embedding);
        sims.push(sim);
        allSimilarities.push(sim);
      }
      sims.sort((a, b) => a - b);

      const mean = sims.reduce((a, b) => a + b, 0) / sims.length;
      const above07 = sims.filter((s) => s > 0.7).length;

      console.log(
        `  ${goldenId.padEnd(25)} | ${mean.toFixed(4)} | ${percentile(sims, 0.5).toFixed(4)} | ${percentile(sims, 0.75).toFixed(4)} | ${percentile(sims, 0.9).toFixed(4)} | ${percentile(sims, 1.0).toFixed(4)} | ${above07}`
      );
    }

    allSimilarities.sort((a, b) => a - b);
    const overallMean = allSimilarities.reduce((a, b) => a + b, 0) / allSimilarities.length;
    const totalAbove07 = allSimilarities.filter((s) => s > 0.7).length;

    console.log(
      `\n  Overall: mean=${overallMean.toFixed(4)}, >0.7 count=${totalAbove07}/${allSimilarities.length} (${((totalAbove07 / allSimilarities.length) * 100).toFixed(1)}%)`
    );
  }

  // Also compute inter-golden similarity for reference
  console.log('\n\n--- Reference: Inter-golden claim similarity ---');
  const refEmbeddings: Array<{ id: string; embedding: readonly number[] }> = [];
  for (const c of TEST_CLAIMS) {
    const emb = await embed(embeddingService, c.text);
    if (emb) refEmbeddings.push({ id: c.id, embedding: emb });
  }

  for (let i = 0; i < refEmbeddings.length; i++) {
    for (let j = i + 1; j < refEmbeddings.length; j++) {
      const sim = cosineSimilarity(refEmbeddings[i]!.embedding, refEmbeddings[j]!.embedding);
      if (sim > 0.6) {
        console.log(`  ${refEmbeddings[i]!.id} <-> ${refEmbeddings[j]!.id}: ${sim.toFixed(4)}`);
      }
    }
  }
}

main().catch(console.error);

/**
 * Diagnostic: Hypothesis 2 - Text Search Keyword Overlap
 *
 * Counts how many synthetic claims match each golden query's keywords via ILIKE,
 * showing text search saturation as corpus grows.
 *
 * Run: npx tsx apps/pce-memory/scripts/benchmark/diagnostics/text-search-overlap.ts
 */

import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from 'yaml';
import { generateClaims } from '../data/synthetic-claims';
import { TEST_CLAIMS } from '../../assay/test-data';

type Query = {
  id: string;
  text: string;
  metadata?: { expected?: Array<string | { path: string; relevance: number }> };
};

function splitWords(query: string): string[] {
  return query.split(/[\s\u3000]+/).filter((w) => w.length > 0);
}

function ilikeMatch(text: string, word: string): boolean {
  return text.toLowerCase().includes(word.toLowerCase());
}

async function main() {
  console.log('=== Hypothesis 2: Text Search Keyword Overlap ===\n');

  const repoRoot = join(import.meta.dirname, '../../..');
  const datasetPath = join(repoRoot, 'tests/eval/goldens/queries.yaml');
  const raw = readFileSync(datasetPath, 'utf-8');
  const dataset = parse(raw) as { queries: Query[] };
  const queries = dataset.queries;

  const goldenIds = new Set(TEST_CLAIMS.map((c) => c.id));

  for (const scalePoint of [15, 100, 500, 1000]) {
    console.log(`\n--- Scale: ${scalePoint} claims ---`);
    const claims = generateClaims(scalePoint);
    const synthetic = claims.filter((c) => !goldenIds.has(c.id));
    const golden = claims.filter((c) => goldenIds.has(c.id));

    console.log(`  Golden: ${golden.length}, Synthetic: ${synthetic.length}`);
    console.log(
      `\n  ${'Query ID'.padEnd(25)} | ${'Query Text'.padEnd(20)} | GoldenMatch | SynthMatch | Total | Ratio`
    );
    console.log(
      `  ${'-'.repeat(25)} | ${'-'.repeat(20)} | ----------- | ---------- | ----- | -----`
    );

    for (const query of queries) {
      const words = splitWords(query.text);

      let goldenMatchCount = 0;
      for (const c of golden) {
        const matches = words.some((w) => ilikeMatch(c.text, w));
        if (matches) goldenMatchCount++;
      }

      let synthMatchCount = 0;
      for (const c of synthetic) {
        const matches = words.some((w) => ilikeMatch(c.text, w));
        if (matches) synthMatchCount++;
      }

      const total = goldenMatchCount + synthMatchCount;
      const ratio = total > 0 ? (synthMatchCount / total).toFixed(2) : 'N/A';

      console.log(
        `  ${query.id.padEnd(25)} | ${query.text.padEnd(20).slice(0, 20)} | ${String(goldenMatchCount).padStart(11)} | ${String(synthMatchCount).padStart(10)} | ${String(total).padStart(5)} | ${String(ratio).padStart(5)}`
      );
    }

    // Summary: how many queries have synthMatchCount > kText (48)?
    let overflowCount = 0;
    for (const query of queries) {
      const words = splitWords(query.text);
      let synthMatchCount = 0;
      for (const c of synthetic) {
        if (words.some((w) => ilikeMatch(c.text, w))) synthMatchCount++;
      }
      if (synthMatchCount > 48) overflowCount++;
    }
    console.log(
      `\n  Queries with synthetic matches > kText(48): ${overflowCount}/${queries.length}`
    );
  }
}

main().catch(console.error);

import { randomUUID } from 'crypto';
import { existsSync, unlinkSync } from 'fs';
import { tmpdir } from 'os';
import { join } from 'path';
import { performance } from 'perf_hooks';
import type { EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { getConnection, initDb, initSchema, resetDbAsync } from '../../src/db/connection';
import type { ScoredClaim } from '../../src/store/hybridSearch';
import { saveClaimVector, setEmbeddingService } from '../../src/store/hybridSearch';
import { upsertClaim } from '../../src/store/claims';
import { updateCritic } from '../../src/store/critic';

export interface BenchmarkClaimInput {
  text: string;
  kind?: 'fact' | 'preference' | 'task' | 'policy_hint';
  scope?: 'session' | 'project' | 'principle';
  boundary_class?: 'public' | 'internal' | 'pii';
  content_hash: string;
  critic?: number;
  embedding?: readonly number[];
  utility?: number;
  confidence?: number;
}

export interface TopKMetrics {
  precision: number;
  recall: number;
  diversity: number;
  latency_ms: number;
  top_ids: string[];
}

export function createLookupEmbeddingService(
  lookup: Record<string, readonly number[]>,
  fallback: readonly number[]
): EmbeddingService {
  return {
    embed: (input: { text: string; sensitivity: string }) => () =>
      Promise.resolve(
        E.right({
          embedding: lookup[input.text] ?? fallback,
          modelVersion: 'precision-benchmark-v1',
        })
      ),
  };
}

export async function resetPrecisionBenchmarkDb(): Promise<string> {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  await new Promise((resolve) => setTimeout(resolve, 25));

  const dbPath = join(tmpdir(), `pce-precision-${randomUUID()}.duckdb`);
  process.env.PCE_DB = dbPath;
  await initDb();
  await initSchema();
  return dbPath;
}

export async function cleanupPrecisionBenchmarkDb(dbPath: string): Promise<void> {
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();

  if (existsSync(dbPath)) {
    try {
      unlinkSync(dbPath);
    } catch {
      // Best-effort cleanup for CI/parallel DuckDB file handles.
    }
  }

  const walPath = `${dbPath}.wal`;
  if (existsSync(walPath)) {
    try {
      unlinkSync(walPath);
    } catch {
      // Best-effort cleanup for CI/parallel DuckDB file handles.
    }
  }

  await new Promise((resolve) => setTimeout(resolve, 50));
}

export async function seedBenchmarkClaim(input: BenchmarkClaimInput): Promise<string> {
  const { claim } = await upsertClaim({
    text: input.text,
    kind: input.kind ?? 'fact',
    scope: input.scope ?? 'project',
    boundary_class: input.boundary_class ?? 'internal',
    content_hash: input.content_hash,
  });

  if (input.critic !== undefined) {
    await updateCritic(claim.id, input.critic, 0, 5);
  }

  if (input.embedding) {
    await saveClaimVector(claim.id, [...input.embedding], 'precision-benchmark-v1');
  }

  if (input.utility !== undefined || input.confidence !== undefined) {
    const conn = await getConnection();
    await conn.run(
      `UPDATE claims
       SET utility = COALESCE($1, utility),
           confidence = COALESCE($2, confidence)
       WHERE id = $3`,
      [input.utility ?? null, input.confidence ?? null, claim.id]
    );
  }

  return claim.id;
}

export function measureTopK(
  results: ScoredClaim[],
  relevantIds: readonly string[],
  clusterByClaimId: Record<string, string>,
  latencyMs: number,
  k: number = 3
): TopKMetrics {
  const top = results.slice(0, k);
  const relevant = new Set(relevantIds);
  const matched = top.filter((result) => relevant.has(result.claim.id));
  const clusters = new Set(
    top
      .map((result) => clusterByClaimId[result.claim.id])
      .filter((value): value is string => !!value)
  );

  return {
    precision: top.length === 0 ? 0 : matched.length / Math.max(top.length, k),
    recall: relevant.size === 0 ? 0 : matched.length / relevant.size,
    diversity: clusters.size,
    latency_ms: latencyMs,
    top_ids: top.map((result) => result.claim.id),
  };
}

export async function runMeasuredSearch(
  search: () => Promise<ScoredClaim[]>,
  repeats: number = 12
): Promise<{ results: ScoredClaim[]; avgLatencyMs: number }> {
  let lastResults: ScoredClaim[] = [];
  const samples: number[] = [];

  for (let i = 0; i < repeats; i++) {
    const startedAt = performance.now();
    lastResults = await search();
    samples.push(performance.now() - startedAt);
  }

  const avgLatencyMs = samples.reduce((sum, value) => sum + value, 0) / Math.max(samples.length, 1);

  return {
    results: lastResults,
    avgLatencyMs,
  };
}

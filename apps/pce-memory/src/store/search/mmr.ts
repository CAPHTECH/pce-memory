/**
 * MMR (Maximal Marginal Relevance) diversification
 */

import { getConnection } from '../../db/connection.js';
import type { RankedSearchResult, MmrConfig } from './types.js';
import { buildSimilarityTokenSet } from './types.js';

function cosineSimilarity(a: readonly number[], b: readonly number[]): number {
  if (a.length === 0 || b.length === 0 || a.length !== b.length) {
    return 0;
  }

  let dot = 0;
  let normA = 0;
  let normB = 0;
  for (let i = 0; i < a.length; i++) {
    const av = a[i]!;
    const bv = b[i]!;
    dot += av * bv;
    normA += av * av;
    normB += bv * bv;
  }

  if (normA === 0 || normB === 0) {
    return 0;
  }

  const similarity = dot / Math.sqrt(normA * normB);
  return Math.max(0, Math.min(1, (similarity + 1) / 2));
}

function jaccardSimilarity(a: Set<string>, b: Set<string>): number {
  if (a.size === 0 || b.size === 0) {
    return 0;
  }

  let intersection = 0;
  for (const token of a) {
    if (b.has(token)) {
      intersection++;
    }
  }

  const union = a.size + b.size - intersection;
  return union === 0 ? 0 : intersection / union;
}

export async function fetchClaimEmbeddings(
  claimIds: readonly string[]
): Promise<Map<string, readonly number[]>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT claim_id, embedding FROM claim_vectors WHERE claim_id IN (${placeholders})`,
    [...claimIds]
  );
  const rows = reader.getRowObjects() as unknown as Array<{
    claim_id: string;
    embedding: number[];
  }>;

  return new Map(
    rows.map((row) => [
      row.claim_id,
      Array.isArray(row.embedding) ? row.embedding.map((value) => Number(value)) : [],
    ])
  );
}

function candidateSimilarity(
  candidate: RankedSearchResult,
  selected: RankedSearchResult,
  embeddings: Map<string, readonly number[]>,
  tokenSets: Map<string, Set<string>>
): number {
  const candidateEmbedding = embeddings.get(candidate.claim.id);
  const selectedEmbedding = embeddings.get(selected.claim.id);
  const vectorSimilarity =
    candidateEmbedding && selectedEmbedding
      ? cosineSimilarity(candidateEmbedding, selectedEmbedding)
      : 0;

  const candidateTokens =
    tokenSets.get(candidate.claim.id) ?? buildSimilarityTokenSet(candidate.claim.text);
  const selectedTokens =
    tokenSets.get(selected.claim.id) ?? buildSimilarityTokenSet(selected.claim.text);

  tokenSets.set(candidate.claim.id, candidateTokens);
  tokenSets.set(selected.claim.id, selectedTokens);

  return Math.max(vectorSimilarity, jaccardSimilarity(candidateTokens, selectedTokens));
}

export function rerankWithMmr(
  results: RankedSearchResult[],
  mmrConfig: Required<MmrConfig>,
  limit: number,
  embeddings: Map<string, readonly number[]>
): RankedSearchResult[] {
  if (results.length <= 1) {
    return results;
  }

  const headSize = Math.min(results.length, Math.max(limit, mmrConfig.maxCandidates));
  const head = results.slice(0, headSize);
  const tail = results.slice(headSize);

  const minScore = Math.min(...head.map((result) => result.fusedScore));
  const maxScore = Math.max(...head.map((result) => result.fusedScore));
  const scoreSpan = Math.max(maxScore - minScore, 0.000001);
  const relevance = new Map(
    head.map((result) => [result.claim.id, (result.fusedScore - minScore) / scoreSpan])
  );
  const tokenSets = new Map<string, Set<string>>();
  const selected: RankedSearchResult[] = [];
  const remaining = [...head];

  while (remaining.length > 0) {
    let bestIndex = 0;
    let bestScore = Number.NEGATIVE_INFINITY;

    for (let i = 0; i < remaining.length; i++) {
      const candidate = remaining[i]!;
      const relevanceScore = relevance.get(candidate.claim.id) ?? 0;
      const redundancyPenalty =
        selected.length === 0
          ? 0
          : Math.max(
              ...selected.map((chosen) =>
                candidateSimilarity(candidate, chosen, embeddings, tokenSets)
              )
            );
      const mmrScore =
        mmrConfig.lambda * relevanceScore - (1 - mmrConfig.lambda) * redundancyPenalty;

      if (
        mmrScore > bestScore ||
        (mmrScore === bestScore &&
          candidate.fusedScore > (remaining[bestIndex]?.fusedScore ?? Number.NEGATIVE_INFINITY))
      ) {
        bestIndex = i;
        bestScore = mmrScore;
      }
    }

    selected.push(remaining.splice(bestIndex, 1)[0]!);
  }

  return [...selected, ...tail];
}

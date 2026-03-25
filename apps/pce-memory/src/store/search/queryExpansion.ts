/**
 * Entity graph query expansion
 */

import { getConnection } from '../../db/connection.js';
import type { QueryExpansionConfig } from './types.js';
import { escapeLikePattern, buildSimilarityTokenSet } from './types.js';

function normalizeExpansionCandidate(value: string | null | undefined): string | undefined {
  if (!value) {
    return undefined;
  }

  const normalized = value.replace(/[-_]+/g, ' ').trim();
  return normalized.length > 0 ? normalized : undefined;
}

export async function expandQueryWithEntityGraph(
  query: string,
  config: Required<QueryExpansionConfig>
): Promise<string> {
  const normalizedQuery = query.trim().toLowerCase();
  if (normalizedQuery.length === 0) {
    return query;
  }

  const queryTokens = [...buildSimilarityTokenSet(query)].slice(0, 8);
  if (queryTokens.length === 0) {
    return query;
  }

  const conn = await getConnection();
  const params: Array<string | number> = [];
  const scoreClauses: string[] = [];
  const whereClauses: string[] = [];

  const pushScoredMatch = (expression: string, value: string, weight: number): void => {
    const paramIndex = params.push(value);
    scoreClauses.push(`CASE WHEN ${expression.replaceAll('?', `$${paramIndex}`)} THEN ${weight} ELSE 0 END`);
    whereClauses.push(expression.replaceAll('?', `$${paramIndex}`));
  };

  pushScoredMatch('LOWER(e.name) = ?', normalizedQuery, 8);
  pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) = ?", normalizedQuery, 10);
  const escapedFullQuery = `%${escapeLikePattern(normalizedQuery)}%`;
  pushScoredMatch("LOWER(e.name) LIKE ? ESCAPE '\\'", escapedFullQuery, 4);
  pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) LIKE ? ESCAPE '\\'", escapedFullQuery, 5);

  for (const token of queryTokens) {
    const escapedToken = `%${escapeLikePattern(token)}%`;
    pushScoredMatch("LOWER(e.name) LIKE ? ESCAPE '\\'", escapedToken, 2);
    pushScoredMatch("LOWER(COALESCE(e.canonical_key, '')) LIKE ? ESCAPE '\\'", escapedToken, 3);
  }

  if (whereClauses.length === 0) {
    return query;
  }

  const seedLimitParam = params.push(config.maxSeedEntities);
  const seedReader = await conn.runAndReadAll(
    `SELECT
       e.id,
       e.name,
       e.canonical_key,
       (${scoreClauses.join(' + ')}) AS match_score
     FROM entities e
     WHERE ${whereClauses.join(' OR ')}
     ORDER BY match_score DESC, e.created_at DESC
     LIMIT $${seedLimitParam}::INTEGER`,
    params
  );
  const seedRows = seedReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
    match_score: number | bigint;
  }>;

  const seedIds = seedRows
    .filter((row) => Number(row.match_score) > 0)
    .map((row) => row.id)
    .slice(0, config.maxSeedEntities);
  if (seedIds.length === 0) {
    return query;
  }

  const seedPlaceholders = seedIds.map((_, index) => `$${index + 1}`).join(',');
  const relatedLimitParam = seedIds.length + 1;
  const relationReader = await conn.runAndReadAll(
    `SELECT DISTINCT e.id, e.name, e.canonical_key
     FROM relations r
     INNER JOIN entities e
       ON (
         (r.src_id IN (${seedPlaceholders}) AND e.id = r.dst_id)
         OR
         (r.dst_id IN (${seedPlaceholders}) AND e.id = r.src_id)
       )
     WHERE e.id NOT IN (${seedPlaceholders})
     ORDER BY e.created_at DESC
     LIMIT $${relatedLimitParam}::INTEGER`,
    [...seedIds, config.maxRelatedEntities]
  );
  const relationRows = relationReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
  }>;

  const coClaimReader = await conn.runAndReadAll(
    `SELECT DISTINCT e.id, e.name, e.canonical_key
     FROM claim_entities seed
     INNER JOIN claim_entities sibling ON sibling.claim_id = seed.claim_id
     INNER JOIN entities e ON e.id = sibling.entity_id
     WHERE seed.entity_id IN (${seedPlaceholders})
       AND sibling.entity_id NOT IN (${seedPlaceholders})
     ORDER BY e.created_at DESC
     LIMIT $${relatedLimitParam}::INTEGER`,
    [...seedIds, config.maxRelatedEntities]
  );
  const coClaimRows = coClaimReader.getRowObjects() as unknown as Array<{
    id: string;
    name: string;
    canonical_key: string | null;
  }>;

  const originalTerms = buildSimilarityTokenSet(query);
  const expansionTerms: string[] = [];
  const seenTerms = new Set<string>();

  for (const row of [...relationRows, ...coClaimRows]) {
    for (const candidate of [
      normalizeExpansionCandidate(row.name),
      normalizeExpansionCandidate(row.canonical_key),
    ]) {
      if (!candidate) {
        continue;
      }

      const candidateTokens = buildSimilarityTokenSet(candidate);
      const introducesNewTerm = [...candidateTokens].some((token) => !originalTerms.has(token));
      const candidateKey = candidate.toLowerCase();

      if (!introducesNewTerm || seenTerms.has(candidateKey)) {
        continue;
      }

      seenTerms.add(candidateKey);
      expansionTerms.push(candidate);

      if (expansionTerms.length >= config.maxExpansionTerms) {
        return `${query} ${expansionTerms.join(' ')}`.trim();
      }
    }
  }

  return expansionTerms.length > 0 ? `${query} ${expansionTerms.join(' ')}`.trim() : query;
}

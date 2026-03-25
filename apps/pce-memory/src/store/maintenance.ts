import * as E from 'fp-ts/Either';
import type { SensitivityLevel } from '@pce/embeddings';
import { getConnection } from '../db/connection.js';
import { getEmbeddingService } from './hybridSearch.js';

export interface MaintenanceHintClaim {
  id: string;
  text: string;
  source_record_type?: string;
  transient?: boolean;
}

export interface SimilarPairHint {
  a: string;
  b: string;
  similarity: number;
  suggestion: 'consider_consolidation';
}

export interface StaleCandidateHint {
  id: string;
  last_retrieved_at: null;
  days_since_created: number;
}

export interface HighRetrievalNoFeedbackHint {
  id: string;
  retrieval_count: number;
  feedback_count: number;
}

export interface MaintenanceHints {
  similar_pairs: SimilarPairHint[];
  stale_candidates: StaleCandidateHint[];
  unprocessed_observations: number;
  high_retrieval_no_feedback: HighRetrievalNoFeedbackHint[];
}

export interface MaintenanceHintOptions {
  similarityThreshold: number;
  staleDays: number;
  highRetrievalThreshold?: number;
  listLimit?: number;
}

const DEFAULT_HIGH_RETRIEVAL_THRESHOLD = 5;
const DEFAULT_LIST_LIMIT = 10;
const MS_PER_DAY = 24 * 60 * 60 * 1000;
const ACTIVE_DURABLE_CLAIM_FILTER = `COALESCE(c.tombstone, FALSE) = FALSE
  AND NOT EXISTS (
    SELECT 1
    FROM promotion_queue pq
    WHERE pq.accepted_claim_id = c.id
      AND pq.status = 'rolled_back'
  )`;

type ClaimVectorRow = {
  claim_id: string;
  embedding: number[] | { items?: number[] } | null;
};

function resolveListLimit(value: number | undefined): number {
  return typeof value === 'number' && Number.isFinite(value) && value > 0
    ? Math.floor(value)
    : DEFAULT_LIST_LIMIT;
}

function resolveHighRetrievalThreshold(value: number | undefined): number {
  return typeof value === 'number' && Number.isFinite(value) && value >= 0
    ? Math.floor(value)
    : DEFAULT_HIGH_RETRIEVAL_THRESHOLD;
}

function normalizeEmbedding(
  embedding: number[] | { items?: number[] } | null | undefined
): readonly number[] | undefined {
  if (Array.isArray(embedding)) {
    return embedding.map((value) => Number(value));
  }

  if (
    embedding &&
    typeof embedding === 'object' &&
    Array.isArray((embedding as { items?: number[] }).items)
  ) {
    return (embedding as { items: number[] }).items.map((value) => Number(value));
  }

  return undefined;
}

function cosineSimilarity(a: readonly number[], b: readonly number[]): number {
  if (a.length === 0 || b.length === 0 || a.length !== b.length) {
    return 0;
  }

  let dot = 0;
  let normA = 0;
  let normB = 0;

  for (let index = 0; index < a.length; index++) {
    const left = a[index] ?? 0;
    const right = b[index] ?? 0;
    dot += left * right;
    normA += left * left;
    normB += right * right;
  }

  if (normA === 0 || normB === 0) {
    return 0;
  }

  const similarity = dot / Math.sqrt(normA * normB);
  return Math.max(0, Math.min(1, similarity));
}

function isDurableReturnedClaim(claim: MaintenanceHintClaim): boolean {
  if (claim.transient === true) {
    return false;
  }

  if (claim.source_record_type === 'observation') {
    return false;
  }

  return typeof claim.id === 'string' && claim.id.startsWith('clm_') && claim.text.length > 0;
}

async function fetchClaimEmbeddings(
  claimIds: readonly string[]
): Promise<Map<string, readonly number[]>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT claim_id, embedding
     FROM claim_vectors
     WHERE claim_id IN (${placeholders})`,
    [...claimIds]
  );
  const rows = reader.getRowObjects() as unknown as ClaimVectorRow[];

  return new Map(
    rows
      .map((row) => {
        const embedding = normalizeEmbedding(row.embedding);
        return embedding ? ([row.claim_id, embedding] as const) : null;
      })
      .filter((row): row is readonly [string, readonly number[]] => row !== null)
  );
}

async function hydrateMissingEmbeddings(
  claims: readonly MaintenanceHintClaim[],
  embeddings: Map<string, readonly number[]>
): Promise<void> {
  const embeddingService = getEmbeddingService();
  if (!embeddingService) {
    return;
  }

  const missingClaims = claims.filter((claim) => !embeddings.has(claim.id));
  for (const claim of missingClaims) {
    const sensitivity: SensitivityLevel = 'internal';
    const result = await embeddingService.embed({
      text: claim.text,
      sensitivity,
      skipCache: true,
    })();
    if (E.isRight(result)) {
      embeddings.set(claim.id, result.right.embedding);
    }
  }
}

async function collectSimilarPairs(
  returnedClaims: readonly MaintenanceHintClaim[],
  similarityThreshold: number,
  listLimit: number
): Promise<SimilarPairHint[]> {
  const durableClaims = returnedClaims.filter(isDurableReturnedClaim);
  if (durableClaims.length < 2) {
    return [];
  }

  const embeddings = await fetchClaimEmbeddings(durableClaims.map((claim) => claim.id));
  await hydrateMissingEmbeddings(durableClaims, embeddings);

  const hints: SimilarPairHint[] = [];

  for (let leftIndex = 0; leftIndex < durableClaims.length; leftIndex++) {
    const left = durableClaims[leftIndex]!;
    const leftEmbedding = embeddings.get(left.id);
    if (!leftEmbedding) {
      continue;
    }

    for (let rightIndex = leftIndex + 1; rightIndex < durableClaims.length; rightIndex++) {
      const right = durableClaims[rightIndex]!;
      const rightEmbedding = embeddings.get(right.id);
      if (!rightEmbedding) {
        continue;
      }

      const similarity = cosineSimilarity(leftEmbedding, rightEmbedding);
      if (similarity > similarityThreshold) {
        hints.push({
          a: left.id,
          b: right.id,
          similarity: Number(similarity.toFixed(4)),
          suggestion: 'consider_consolidation',
        });
      }
    }
  }

  return hints.sort((a, b) => b.similarity - a.similarity).slice(0, listLimit);
}

async function collectStaleCandidates(
  staleDays: number,
  listLimit: number
): Promise<StaleCandidateHint[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT c.id, c.created_at
     FROM claims c
     LEFT JOIN active_context_items aci ON aci.claim_id = c.id
     WHERE ${ACTIVE_DURABLE_CLAIM_FILTER}
       AND c.created_at < CURRENT_TIMESTAMP - INTERVAL '${staleDays} days'
     GROUP BY c.id, c.created_at
     HAVING COUNT(aci.id) = 0
     ORDER BY c.created_at ASC
     LIMIT $1`,
    [listLimit]
  );

  const rows = reader.getRowObjects() as Array<{ id: string; created_at: Date | string }>;
  const now = Date.now();

  return rows.map((row) => ({
    id: row.id,
    last_retrieved_at: null,
    days_since_created: Math.max(
      staleDays,
      Math.floor((now - new Date(row.created_at).getTime()) / MS_PER_DAY)
    ),
  }));
}

async function countUnprocessedObservations(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT COUNT(*)::INTEGER AS count
     FROM observations
     WHERE content IS NOT NULL
       AND (expires_at IS NULL OR expires_at > CURRENT_TIMESTAMP)`
  );
  const rows = reader.getRowObjects() as Array<{ count: number | bigint }>;
  return Number(rows[0]?.count ?? 0);
}

async function collectHighRetrievalNoFeedback(
  threshold: number,
  listLimit: number
): Promise<HighRetrievalNoFeedbackHint[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT
       c.id,
       ac.retrieval_count,
       COALESCE(fb.feedback_count, 0) AS feedback_count
     FROM claims c
     INNER JOIN (
       SELECT claim_id, COUNT(*)::INTEGER AS retrieval_count
       FROM active_context_items
       GROUP BY claim_id
     ) ac ON ac.claim_id = c.id
     LEFT JOIN (
       SELECT claim_id, COUNT(*)::INTEGER AS feedback_count
       FROM feedback
       GROUP BY claim_id
     ) fb ON fb.claim_id = c.id
     WHERE ${ACTIVE_DURABLE_CLAIM_FILTER}
       AND ac.retrieval_count > $1
       AND COALESCE(fb.feedback_count, 0) = 0
     ORDER BY ac.retrieval_count DESC, c.created_at ASC
     LIMIT $2`,
    [threshold, listLimit]
  );

  const rows = reader.getRowObjects() as Array<{
    id: string;
    retrieval_count: number | bigint;
    feedback_count: number | bigint;
  }>;

  return rows.map((row) => ({
    id: row.id,
    retrieval_count: Number(row.retrieval_count),
    feedback_count: Number(row.feedback_count),
  }));
}

export async function collectMaintenanceHints(
  returnedClaims: readonly MaintenanceHintClaim[],
  options: MaintenanceHintOptions
): Promise<MaintenanceHints> {
  const listLimit = resolveListLimit(options.listLimit);
  const highRetrievalThreshold = resolveHighRetrievalThreshold(options.highRetrievalThreshold);
  const similar_pairs = await collectSimilarPairs(
    returnedClaims,
    options.similarityThreshold,
    listLimit
  );
  const stale_candidates = await collectStaleCandidates(options.staleDays, listLimit);
  const unprocessed_observations = await countUnprocessedObservations();
  const high_retrieval_no_feedback = await collectHighRetrievalNoFeedback(
    highRetrievalThreshold,
    listLimit
  );

  return {
    similar_pairs,
    stale_candidates,
    unprocessed_observations,
    high_retrieval_no_feedback,
  };
}

import type { DuckDBConnection } from '@duckdb/node-api';
import { withDedicatedConnection } from '../db/connection.js';
import type { ClaimKind, ClaimStatus, MemoryType } from '../domain/types.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';

export const CLAIM_LINK_TYPES = [
  'extends',
  'supports',
  'contradicts',
  'supersedes',
  'related',
] as const;

export type ClaimLinkType = (typeof CLAIM_LINK_TYPES)[number];
export type ClaimLinkCreatedBy = 'client' | 'auto_similarity';

export interface ClaimLink {
  id: string;
  source_claim_id: string;
  target_claim_id: string;
  link_type: ClaimLinkType;
  confidence: number;
  created_at: string;
  created_by?: ClaimLinkCreatedBy | null;
}

interface ClaimLinkRow extends Omit<ClaimLink, 'created_at'> {
  created_at: string | Date;
}

export interface ClaimLinkSuggestion {
  target: string;
  similarity: number;
  suggested_type: 'related';
}

export interface ClaimLinkHop {
  link_id: string;
  seed_claim_id: string;
  connected_claim_id: string;
  link_type: ClaimLinkType;
  confidence: number;
}

export interface ClaimLinkSearchFilters {
  scopes: string[];
  boundaryClasses: string[];
  kindFilter?: ClaimKind[];
  memoryTypeFilter?: MemoryType[];
  excludedWorkingStateStatuses?: ClaimStatus[];
}

function activeClaimFilter(alias: string): string {
  return `COALESCE(${alias}.tombstone, FALSE) = FALSE
    AND NOT EXISTS (
      SELECT 1
      FROM promotion_queue pq
      WHERE pq.accepted_claim_id = ${alias}.id
        AND pq.status = 'rolled_back'
    )`;
}

function normalizeConfidence(value: number | undefined): number {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    return 1.0;
  }
  return Math.max(0, Math.min(1, value));
}

function normalizeClaimLinkRow(row: ClaimLinkRow): ClaimLink {
  const normalized = normalizeRowsTimestamps([row], ['created_at'])[0]!;
  return {
    id: normalized.id,
    source_claim_id: normalized.source_claim_id,
    target_claim_id: normalized.target_claim_id,
    link_type: normalized.link_type,
    confidence: Number(normalized.confidence),
    created_at: String(normalized.created_at),
    created_by: normalized.created_by ?? null,
  };
}

async function readClaimVector(
  connection: DuckDBConnection,
  claimId: string
): Promise<readonly number[] | undefined> {
  const reader = await connection.runAndReadAll(
    'SELECT embedding FROM claim_vectors WHERE claim_id = $1',
    [claimId]
  );
  const rows = reader.getRowObjects();
  if (rows.length === 0) {
    return undefined;
  }

  const row = rows[0] as Record<string, unknown>;
  const embedding = row['embedding'];
  if (embedding == null) {
    return undefined;
  }
  if (Array.isArray(embedding)) {
    return embedding as number[];
  }
  if (typeof embedding === 'object' && 'items' in embedding) {
    const listValue = embedding as { items: number[] };
    if (Array.isArray(listValue.items)) {
      return listValue.items;
    }
  }

  return undefined;
}

export function isValidClaimLinkType(value: unknown): value is ClaimLinkType {
  return typeof value === 'string' && CLAIM_LINK_TYPES.includes(value as ClaimLinkType);
}

export async function upsertClaimLink(input: {
  source_claim_id: string;
  target_claim_id: string;
  link_type: ClaimLinkType;
  confidence?: number;
  created_by?: ClaimLinkCreatedBy;
}): Promise<{ link: ClaimLink; isNew: boolean }> {
  const confidence = normalizeConfidence(input.confidence);
  const createdBy = input.created_by ?? 'client';

  return withDedicatedConnection(async (conn) => {
    try {
      // Attempt INSERT first
      const id = `clk_${crypto.randomUUID().slice(0, 8)}`;
      const createdAt = new Date().toISOString();
      await conn.run(
        `INSERT INTO claim_links (
          id, source_claim_id, target_claim_id, link_type, confidence, created_at, created_by
        ) VALUES ($1, $2, $3, $4, $5, $6, $7)`,
        [
          id,
          input.source_claim_id,
          input.target_claim_id,
          input.link_type,
          confidence,
          createdAt,
          createdBy,
        ]
      );

      return {
        link: {
          id,
          source_claim_id: input.source_claim_id,
          target_claim_id: input.target_claim_id,
          link_type: input.link_type,
          confidence,
          created_at: createdAt,
          created_by: createdBy,
        },
        isNew: true,
      };
    } catch (e: unknown) {
      // UNIQUE constraint violation: link already exists (concurrent insert won).
      // Fall through to SELECT + UPDATE on a fresh connection.
      const isConstraintViolation =
        e instanceof Error &&
        (e.message.includes('UNIQUE constraint') ||
          e.message.includes('unique constraint') ||
          e.message.includes('Duplicate key') ||
          e.message.includes('duplicate key') ||
          e.message.includes('PRIMARY KEY'));
      if (!isConstraintViolation) {
        throw e;
      }
    }

    // Re-read on a fresh connection to avoid poisoned transaction state
    return withDedicatedConnection(async (freshConn) => {
      await freshConn.run(
        `UPDATE claim_links
         SET confidence = $1, created_by = $2
         WHERE source_claim_id = $3
           AND target_claim_id = $4
           AND link_type = $5`,
        [confidence, createdBy, input.source_claim_id, input.target_claim_id, input.link_type]
      );
      const reader = await freshConn.runAndReadAll(
        `SELECT id, source_claim_id, target_claim_id, link_type, confidence, created_at, created_by
         FROM claim_links
         WHERE source_claim_id = $1
           AND target_claim_id = $2
           AND link_type = $3`,
        [input.source_claim_id, input.target_claim_id, input.link_type]
      );
      const rows = reader.getRowObjects() as unknown as ClaimLinkRow[];
      if (!rows[0]) {
        throw new Error(
          `claim_link not found after constraint conflict: ${input.source_claim_id} -> ${input.target_claim_id} (${input.link_type})`
        );
      }
      return {
        link: normalizeClaimLinkRow(rows[0]),
        isNew: false,
      };
    });
  });
}

export async function findOneHopClaimLinks(seedClaimIds: string[]): Promise<ClaimLinkHop[]> {
  if (seedClaimIds.length === 0) {
    return [];
  }

  return withDedicatedConnection(async (conn) => {
    const sourcePlaceholders = seedClaimIds.map((_, index) => `$${index + 1}`).join(',');
    const targetPlaceholders = seedClaimIds
      .map((_, index) => `$${seedClaimIds.length + index + 1}`)
      .join(',');
    const sql = `
      SELECT
        cl.id as link_id,
        cl.source_claim_id as seed_claim_id,
        cl.target_claim_id as connected_claim_id,
        cl.link_type,
        cl.confidence
      FROM claim_links cl
      WHERE cl.source_claim_id IN (${sourcePlaceholders})

      UNION ALL

      SELECT
        cl.id as link_id,
        cl.target_claim_id as seed_claim_id,
        cl.source_claim_id as connected_claim_id,
        cl.link_type,
        cl.confidence
      FROM claim_links cl
      WHERE cl.target_claim_id IN (${targetPlaceholders})
    `;

    const reader = await conn.runAndReadAll(sql, [...seedClaimIds, ...seedClaimIds]);
    const rows = reader.getRowObjects() as unknown as Array<{
      link_id: string;
      seed_claim_id: string;
      connected_claim_id: string;
      link_type: ClaimLinkType;
      confidence: number;
    }>;

    return rows.map((row) => ({
      link_id: row.link_id,
      seed_claim_id: row.seed_claim_id,
      connected_claim_id: row.connected_claim_id,
      link_type: row.link_type,
      confidence: Number(row.confidence),
    }));
  });
}

export async function suggestRelatedClaimLinks(
  sourceClaimId: string,
  options: {
    minSimilarity?: number;
    maxSimilarityExclusive?: number;
    limit?: number;
  } = {}
): Promise<ClaimLinkSuggestion[]> {
  const minSimilarity = options.minSimilarity ?? 0.7;
  const maxSimilarityExclusive = options.maxSimilarityExclusive ?? 0.85;
  const limit = Math.max(1, Math.floor(options.limit ?? 5));
  return withDedicatedConnection(async (conn) => {
    const sourceVector = await readClaimVector(conn, sourceClaimId);
    if (!sourceVector || sourceVector.length === 0) {
      return [];
    }

    const embeddingLiteral = `[${sourceVector.join(',')}]`;
    const reader = await conn.runAndReadAll(
      `
        SELECT candidate_id as target, similarity
        FROM (
          SELECT
            c.id as candidate_id,
            c.created_at,
            norm_cos(cos_sim(cv.embedding, ${embeddingLiteral}::DOUBLE[])) as similarity
          FROM claim_vectors cv
          INNER JOIN claims c ON c.id = cv.claim_id
          WHERE cv.claim_id <> $1
            AND ${activeClaimFilter('c')}
            AND NOT EXISTS (
              SELECT 1
              FROM claim_links cl
              WHERE (cl.source_claim_id = $1 AND cl.target_claim_id = c.id)
                 OR (cl.source_claim_id = c.id AND cl.target_claim_id = $1)
            )
        ) ranked
        WHERE similarity >= $2
          AND similarity < $3
        ORDER BY similarity DESC, created_at DESC, target ASC
        LIMIT $4
      `,
      [sourceClaimId, minSimilarity, maxSimilarityExclusive, limit]
    );
    const rows = reader.getRowObjects() as unknown as Array<{
      target: string;
      similarity: number;
    }>;

    return rows.map((row) => ({
      target: row.target,
      similarity: Number(Number(row.similarity).toFixed(4)),
      suggested_type: 'related',
    }));
  });
}

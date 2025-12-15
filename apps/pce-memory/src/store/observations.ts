/**
 * Observation Store（Issue #30）
 * - Observation（生データ）を短期TTLで保持
 * - 期限後は content を scrub（NULL化）して最小証跡（digest等）のみ残す
 */
import { getConnection } from '../db/connection.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';

export type ObservationSourceType = 'chat' | 'tool' | 'file' | 'http' | 'system';

export interface Observation {
  id: string;
  source_type: ObservationSourceType;
  source_id?: string;
  content?: string | null;
  content_digest: string;
  content_length: number;
  actor?: string;
  tags?: unknown;
  created_at?: Date | string;
  expires_at?: Date | string;
}

export interface InsertObservationInput {
  id: string;
  source_type: ObservationSourceType;
  source_id?: string;
  content: string | null;
  content_digest: string;
  content_length: number;
  actor?: string;
  tags?: string[];
  expires_at: string;
}

export async function insertObservation(input: InsertObservationInput): Promise<Observation> {
  const conn = await getConnection();
  const tagsJson = input.tags ? JSON.stringify(input.tags) : null;

  await conn.run(
    'INSERT INTO observations (id, source_type, source_id, content, content_digest, content_length, actor, tags, expires_at) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9::TIMESTAMP)',
    [
      input.id,
      input.source_type,
      input.source_id ?? null,
      input.content,
      input.content_digest,
      input.content_length,
      input.actor ?? null,
      tagsJson,
      input.expires_at,
    ]
  );

  const reader = await conn.runAndReadAll(
    'SELECT id, source_type, source_id, content, content_digest, content_length, actor, tags, created_at, expires_at FROM observations WHERE id = $1',
    [input.id]
  );
  const rawRows = reader.getRowObjects() as unknown as Observation[];
  const rows = normalizeRowsTimestamps(rawRows);
  return rows[0]!;
}

export async function findObservationById(id: string): Promise<Observation | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, source_type, source_id, content, content_digest, content_length, actor, tags, created_at, expires_at FROM observations WHERE id = $1',
    [id]
  );
  const rawRows = reader.getRowObjects() as unknown as Observation[];
  const rows = normalizeRowsTimestamps(rawRows);
  return rows[0];
}

export type ObservationGcMode = 'scrub' | 'delete';

/**
 * 期限切れObservationのGC
 * - scrub: contentをNULL化（推奨）
 * - delete: row削除（監査目的での保持が不要な場合）
 */
export async function gcExpiredObservations(mode: ObservationGcMode = 'scrub'): Promise<void> {
  const conn = await getConnection();
  if (mode === 'delete') {
    await conn.run(
      'DELETE FROM observations WHERE expires_at IS NOT NULL AND expires_at <= CURRENT_TIMESTAMP'
    );
    return;
  }
  await conn.run(
    'UPDATE observations SET content = NULL WHERE expires_at IS NOT NULL AND expires_at <= CURRENT_TIMESTAMP AND content IS NOT NULL'
  );
}

#!/usr/bin/env tsx

import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { closeDb, getConnection, initDb, initSchema } from '../src/db/connection.ts';
import { isValidMemoryType, type MemoryType } from '../src/domain/types.ts';
import { getEvidenceForClaims } from '../src/store/evidence.ts';
import { normalizeRowsTimestamps } from '../src/utils/serialization.ts';

interface MigrationClaimRow {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  memory_type?: string | null;
  content_hash: string;
  utility: number;
  confidence: number;
  created_at: string;
  updated_at: string;
  recency_anchor?: string | null;
  provenance?: string | Record<string, unknown> | null;
  tombstone?: boolean | null;
  tombstone_at?: string | null;
  rollback_reason?: string | null;
  superseded_by?: string | null;
}

interface PromotionQueueLookupRow {
  id: string;
}

interface MigrationReportItem {
  claim_id: string;
  mapped_memory_type: MemoryType;
}

interface SessionQueueReportItem {
  claim_id: string;
  candidate_id: string;
  source_kind: string;
  proposed_scope: 'project';
  proposed_memory_type: 'working_state';
}

interface SessionTombstoneReportItem {
  claim_id: string;
  reason: string;
}

export interface V2MemoryTypeMigrationReport {
  run_at: string;
  stale_after_days: number;
  summary: {
    total_claims_scanned: number;
    memory_type_backfilled: number;
    memory_type_already_set: number;
    session_claims_scanned: number;
    session_queue_candidates_created: number;
    session_queue_candidates_existing: number;
    session_claims_tombstoned: number;
    session_claims_already_tombstoned: number;
  };
  mapped_counts: Record<MemoryType, number>;
  mapped_claims: MigrationReportItem[];
  ambiguous_preferences: string[];
  session_queue_candidates: SessionQueueReportItem[];
  tombstoned_session_claims: SessionTombstoneReportItem[];
}

export interface V2MemoryTypeMigrationOptions {
  now?: Date | string;
  staleAfterDays?: number;
}

function resolveNow(input?: Date | string): Date {
  if (input instanceof Date) {
    return input;
  }
  if (typeof input === 'string') {
    return new Date(input);
  }
  return new Date();
}

function parseProvenance(value: MigrationClaimRow['provenance']): Record<string, unknown> | null {
  if (!value) {
    return null;
  }
  if (typeof value === 'string') {
    try {
      return JSON.parse(value) as Record<string, unknown>;
    } catch {
      return { raw: value };
    }
  }
  return value;
}

function resolveBackfilledMemoryType(claim: Pick<MigrationClaimRow, 'kind' | 'scope'>): {
  memoryType: MemoryType;
  ambiguousPreference: boolean;
} {
  if (claim.scope === 'principle' || claim.kind === 'policy_hint') {
    return { memoryType: 'norm', ambiguousPreference: false };
  }

  switch (claim.kind) {
    case 'task':
      return { memoryType: 'working_state', ambiguousPreference: false };
    case 'fact':
      return { memoryType: 'knowledge', ambiguousPreference: false };
    case 'preference':
      return { memoryType: 'procedure', ambiguousPreference: true };
    default:
      return { memoryType: 'knowledge', ambiguousPreference: false };
  }
}

function getSessionMigrationCandidateId(claimId: string): string {
  return `pq_mig_${claimId.replace(/^clm_/, '')}`;
}

function buildSessionMigrationCandidateHash(
  claim: Pick<MigrationClaimRow, 'id' | 'content_hash'>
): string {
  return claim.content_hash;
}

function resolveRecencyAnchor(claim: MigrationClaimRow): Date | null {
  const candidate = claim.recency_anchor ?? claim.created_at;
  if (!candidate) {
    return null;
  }
  const parsed = new Date(candidate);
  return Number.isNaN(parsed.getTime()) ? null : parsed;
}

function buildMappedCounts(): Record<MemoryType, number> {
  return {
    evidence: 0,
    knowledge: 0,
    norm: 0,
    procedure: 0,
    working_state: 0,
  };
}

let migrationQueue: Promise<unknown> = Promise.resolve();

function runSerializedMigration<T>(task: () => Promise<T>): Promise<T> {
  const previous = migrationQueue.catch(() => undefined);
  const current = previous.then(task);
  migrationQueue = current.then(
    () => undefined,
    () => undefined
  );
  return current;
}

async function migrateV2MemoryTypeUnlocked(
  options: V2MemoryTypeMigrationOptions = {}
): Promise<V2MemoryTypeMigrationReport> {
  const conn = await getConnection();
  const now = resolveNow(options.now);
  const nowIso = now.toISOString();
  const staleAfterDays = options.staleAfterDays ?? 30;
  const staleThresholdMs = staleAfterDays * 24 * 60 * 60 * 1000;

  const report: V2MemoryTypeMigrationReport = {
    run_at: nowIso,
    stale_after_days: staleAfterDays,
    summary: {
      total_claims_scanned: 0,
      memory_type_backfilled: 0,
      memory_type_already_set: 0,
      session_claims_scanned: 0,
      session_queue_candidates_created: 0,
      session_queue_candidates_existing: 0,
      session_claims_tombstoned: 0,
      session_claims_already_tombstoned: 0,
    },
    mapped_counts: buildMappedCounts(),
    mapped_claims: [],
    ambiguous_preferences: [],
    session_queue_candidates: [],
    tombstoned_session_claims: [],
  };

  await conn.run('BEGIN TRANSACTION');

  try {
    const reader = await conn.runAndReadAll(
      `SELECT
         id, text, kind, scope, boundary_class, memory_type, content_hash,
         utility, confidence, created_at, updated_at, recency_anchor,
         provenance, tombstone, tombstone_at, rollback_reason, superseded_by
       FROM claims
       ORDER BY created_at, id`
    );
    const rawRows = reader.getRowObjects() as MigrationClaimRow[];
    const claims = normalizeRowsTimestamps(rawRows) as MigrationClaimRow[];
    const sessionClaims = claims.filter((claim) => claim.scope === 'session');
    const sessionEvidenceMap = await getEvidenceForClaims(sessionClaims.map((claim) => claim.id));
    const rolledBackReader = await conn.runAndReadAll(
      `SELECT accepted_claim_id
       FROM promotion_queue
       WHERE status = 'rolled_back'
         AND accepted_claim_id IS NOT NULL`
    );
    const rolledBackClaimIds = new Set(
      (
        rolledBackReader.getRowObjects() as Array<{
          accepted_claim_id: string | null;
        }>
      )
        .map((row) => row.accepted_claim_id)
        .filter((claimId): claimId is string => typeof claimId === 'string' && claimId.length > 0)
    );

    report.summary.total_claims_scanned = claims.length;

    for (const claim of claims) {
      const { memoryType, ambiguousPreference } = resolveBackfilledMemoryType(claim);
      const existingMemoryType = isValidMemoryType(claim.memory_type) ? claim.memory_type : null;
      const effectiveMemoryType = existingMemoryType ?? memoryType;
      report.mapped_counts[effectiveMemoryType] += 1;

      if (ambiguousPreference && existingMemoryType === null) {
        report.ambiguous_preferences.push(claim.id);
      }

      if (existingMemoryType === null) {
        await conn.run(
          `UPDATE claims
           SET memory_type = $1,
               updated_at = CURRENT_TIMESTAMP
           WHERE id = $2`,
          [memoryType, claim.id]
        );
        report.summary.memory_type_backfilled += 1;
        report.mapped_claims.push({
          claim_id: claim.id,
          mapped_memory_type: memoryType,
        });
      } else {
        report.summary.memory_type_already_set += 1;
      }

      if (claim.scope !== 'session') {
        continue;
      }

      report.summary.session_claims_scanned += 1;

      if (claim.tombstone || rolledBackClaimIds.has(claim.id)) {
        report.summary.session_claims_already_tombstoned += 1;
        continue;
      }

      const recencyAnchor = resolveRecencyAnchor(claim);
      const isStale =
        recencyAnchor === null || now.getTime() - recencyAnchor.getTime() > staleThresholdMs;

      const existingQueueReader = await conn.runAndReadAll(
        'SELECT id FROM promotion_queue WHERE id = $1',
        [getSessionMigrationCandidateId(claim.id)]
      );
      const existingQueue = (existingQueueReader.getRowObjects() as PromotionQueueLookupRow[])[0];

      if (isStale) {
        const reason = `v2 migration: tombstoned stale session claim (recency_anchor > ${staleAfterDays}d)`;

        await conn.run(
          `UPDATE claims
           SET tombstone = TRUE,
               tombstone_at = COALESCE(tombstone_at, $1::TIMESTAMP),
               rollback_reason = COALESCE(rollback_reason, $2),
               updated_at = CURRENT_TIMESTAMP
           WHERE id = $3`,
          [nowIso, reason, claim.id]
        );
        report.summary.session_claims_tombstoned += 1;
        report.tombstoned_session_claims.push({ claim_id: claim.id, reason });
        continue;
      }

      const candidateId = getSessionMigrationCandidateId(claim.id);
      if (existingQueue) {
        report.summary.session_queue_candidates_existing += 1;
      } else {
        const evidenceIds = (sessionEvidenceMap.get(claim.id) ?? []).map((evidence) => evidence.id);
        await conn.run(
          `INSERT INTO promotion_queue (
             id, source_layer, target_layer, source_ids, distilled_text, candidate_hash,
             proposed_kind, proposed_scope, proposed_boundary_class, proposed_memory_type,
             provenance, evidence_ids, policy_version_checked, boundary_check_result,
             status, created_at
           ) VALUES (
             $1, $2, $3, $4, $5, $6,
             $7, $8, $9, $10,
             $11, $12, $13, $14,
             $15, $16
           )`,
          [
            candidateId,
            'micro',
            'meso',
            JSON.stringify([claim.id]),
            claim.text,
            buildSessionMigrationCandidateHash(claim),
            claim.kind,
            'project',
            claim.boundary_class,
            'working_state',
            JSON.stringify({
              migrated_at: nowIso,
              migration: {
                source_claim_id: claim.id,
                original_scope: claim.scope,
                original_memory_type: effectiveMemoryType,
                original_confidence: claim.confidence,
                original_utility: claim.utility,
                recency_anchor: claim.recency_anchor ?? claim.created_at,
              },
              source_claim_ids: [claim.id],
              original_provenance: parseProvenance(claim.provenance),
            }),
            JSON.stringify(evidenceIds),
            'v2-memory-type-migration',
            JSON.stringify({ allowed: true, migration: true, source_claim_id: claim.id }),
            'pending',
            nowIso,
          ]
        );
        report.summary.session_queue_candidates_created += 1;
      }

      const routeReason = `v2 migration: routed recent session claim to promotion_queue ${candidateId}`;
      await conn.run(
        `UPDATE claims
         SET tombstone = TRUE,
             tombstone_at = COALESCE(tombstone_at, $1::TIMESTAMP),
             rollback_reason = COALESCE(rollback_reason, $2),
             updated_at = CURRENT_TIMESTAMP
         WHERE id = $3`,
        [nowIso, routeReason, claim.id]
      );
      report.summary.session_claims_tombstoned += 1;
      report.tombstoned_session_claims.push({ claim_id: claim.id, reason: routeReason });

      report.session_queue_candidates.push({
        claim_id: claim.id,
        candidate_id: candidateId,
        source_kind: claim.kind,
        proposed_scope: 'project',
        proposed_memory_type: 'working_state',
      });
    }

    await conn.run('COMMIT');
    return report;
  } catch (error) {
    await conn.run('ROLLBACK');
    throw error;
  }
}

export async function migrateV2MemoryType(
  options: V2MemoryTypeMigrationOptions = {}
): Promise<V2MemoryTypeMigrationReport> {
  return runSerializedMigration(() => migrateV2MemoryTypeUnlocked(options));
}

async function main(): Promise<void> {
  await initDb();
  await initSchema();

  try {
    const report = await migrateV2MemoryType();
    console.log(JSON.stringify(report, null, 2));
  } finally {
    await closeDb();
  }
}

function isDirectExecution(metaUrl: string): boolean {
  const currentPath = fileURLToPath(metaUrl);
  const entryPath = process.argv[1] ? resolve(process.argv[1]) : '';
  return currentPath === entryPath;
}

if (isDirectExecution(import.meta.url)) {
  main().catch((error: unknown) => {
    const message = error instanceof Error ? (error.stack ?? error.message) : String(error);
    console.error(message);
    process.exitCode = 1;
  });
}

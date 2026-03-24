import { beforeEach, describe, expect, it } from 'vitest';
import * as E from 'fp-ts/Either';
import {
  getConnection,
  initDb,
  initSchema,
  resetDbAsync,
} from '../src/db/connection';
import { handleUpsert } from '../src/core/handlers';
import { applyPolicyOp, resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { insertEvidence } from '../src/store/evidence';
import { findClaimById, upsertClaim } from '../src/store/claims';
import { initRateState, resetRates } from '../src/store/rate';
import { migrateV2MemoryType } from '../scripts/migrate-v2-memory-type.ts';

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

async function seedClaim(input: Parameters<typeof upsertClaim>[0]) {
  const { claim } = await upsertClaim(input);
  return claim;
}

async function setRecencyAnchor(claimId: string, value: string) {
  const conn = await getConnection();
  await conn.run(
    'UPDATE claims SET recency_anchor = $1::TIMESTAMP, created_at = $1::TIMESTAMP WHERE id = $2',
    [value, claimId]
  );
}

async function setLegacyClaimState(
  claimId: string,
  input: {
    createdAt?: string;
    recencyAnchor?: string | null;
    memoryType?: string | null;
    tombstone?: boolean;
    tombstoneAt?: string | null;
    rollbackReason?: string | null;
  }
) {
  const conn = await getConnection();
  await conn.run(
    `UPDATE claims
     SET created_at = COALESCE($1::TIMESTAMP, created_at),
         recency_anchor = CASE
           WHEN $2 IS NULL THEN NULL
           ELSE $2::TIMESTAMP
         END,
         memory_type = $3,
         tombstone = COALESCE($4, tombstone),
         tombstone_at = CASE
           WHEN $5 IS NULL THEN tombstone_at
           ELSE $5::TIMESTAMP
         END,
         rollback_reason = COALESCE($6, rollback_reason)
     WHERE id = $7`,
    [
      input.createdAt ?? null,
      input.recencyAnchor ?? null,
      input.memoryType ?? null,
      input.tombstone ?? null,
      input.tombstoneAt ?? null,
      input.rollbackReason ?? null,
      claimId,
    ]
  );
}

describe('v2 memory_type migration', () => {
  it('reports zero work for an empty database', async () => {
    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    expect(report.summary).toEqual({
      total_claims_scanned: 0,
      memory_type_backfilled: 0,
      memory_type_already_set: 0,
      session_claims_scanned: 0,
      session_queue_candidates_created: 0,
      session_queue_candidates_existing: 0,
      session_claims_tombstoned: 0,
      session_claims_already_tombstoned: 0,
    });
    expect(report.mapped_counts).toEqual({
      evidence: 0,
      knowledge: 0,
      norm: 0,
      procedure: 0,
      working_state: 0,
    });
    expect(report.mapped_claims).toEqual([]);
    expect(report.ambiguous_preferences).toEqual([]);
  });

  it('maps durable claims to the expected memory_type taxonomy', async () => {
    const fact = await seedClaim({
      text: 'Architecture decisions are durable knowledge',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'a'.repeat(64),
    });
    const task = await seedClaim({
      text: 'Current task is implementing the migration',
      kind: 'task',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'b'.repeat(64),
    });
    const policyHint = await seedClaim({
      text: 'PII should stay internal by default',
      kind: 'policy_hint',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'c'.repeat(64),
    });
    const principleFact = await seedClaim({
      text: 'Prefer reviewable promotion over direct persistence',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'public',
      content_hash: 'sha256:' + 'd'.repeat(64),
    });
    const preference = await seedClaim({
      text: 'Use Vitest for migration tests',
      kind: 'preference',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'e'.repeat(64),
    });

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    expect(report.summary.memory_type_backfilled).toBe(5);
    expect(report.mapped_counts.knowledge).toBe(1);
    expect(report.mapped_counts.working_state).toBe(1);
    expect(report.mapped_counts.norm).toBe(2);
    expect(report.mapped_counts.procedure).toBe(1);
    expect(report.ambiguous_preferences).toContain(preference.id);

    expect((await findClaimById(fact.id))?.memory_type).toBe('knowledge');
    expect((await findClaimById(task.id))?.memory_type).toBe('working_state');
    expect((await findClaimById(policyHint.id))?.memory_type).toBe('norm');
    expect((await findClaimById(principleFact.id))?.memory_type).toBe('norm');
    expect((await findClaimById(preference.id))?.memory_type).toBe('procedure');
  });

  it('migrates principle-only databases without session side effects', async () => {
    const principleFact = await seedClaim({
      text: 'Reviewed principle facts belong to macro memory',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'public',
      content_hash: 'sha256:' + '6'.repeat(64),
    });
    const principlePolicy = await seedClaim({
      text: 'Policy hints become norms',
      kind: 'policy_hint',
      scope: 'principle',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '7'.repeat(64),
    });

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    expect(report.summary.total_claims_scanned).toBe(2);
    expect(report.summary.memory_type_backfilled).toBe(2);
    expect(report.summary.session_claims_scanned).toBe(0);
    expect(report.summary.session_queue_candidates_created).toBe(0);
    expect(report.summary.session_claims_tombstoned).toBe(0);
    expect(report.mapped_counts.norm).toBe(2);
    expect((await findClaimById(principleFact.id))?.memory_type).toBe('norm');
    expect((await findClaimById(principlePolicy.id))?.memory_type).toBe('norm');
  });

  it('backfills only missing memory_type values and reports counts from effective stored types', async () => {
    const missingFact = await seedClaim({
      text: 'Legacy facts need a derived memory type',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '8'.repeat(64),
    });
    const explicitNullTask = await seedClaim({
      text: 'Legacy task with explicit NULL memory_type',
      kind: 'task',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '9'.repeat(64),
      memory_type: 'working_state',
    });
    const typedPreference = await seedClaim({
      text: 'Existing reviewed preference already classified as knowledge',
      kind: 'preference',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'a'.repeat(64),
      memory_type: 'knowledge',
    });

    await setLegacyClaimState(explicitNullTask.id, { memoryType: null, recencyAnchor: null });

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    expect(report.summary.memory_type_backfilled).toBe(2);
    expect(report.summary.memory_type_already_set).toBe(1);
    expect(report.mapped_counts.knowledge).toBe(2);
    expect(report.mapped_counts.working_state).toBe(1);
    expect(report.ambiguous_preferences).toEqual([]);
    expect((await findClaimById(missingFact.id))?.memory_type).toBe('knowledge');
    expect((await findClaimById(explicitNullTask.id))?.memory_type).toBe('working_state');
    expect((await findClaimById(typedPreference.id))?.memory_type).toBe('knowledge');
  });

  it('routes recent session claims to promotion_queue and tombstones stale ones', async () => {
    const recentSession = await seedClaim({
      text: 'We are blocked on the migration review',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'f'.repeat(64),
      provenance: { at: '2026-03-20T12:00:00.000Z', actor: 'claude' },
    });
    const staleSession = await seedClaim({
      text: 'Old local note that should expire',
      kind: 'preference',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '0'.repeat(64),
    });

    await insertEvidence({
      id: 'evd_recent_session',
      claim_id: recentSession.id,
      source_type: 'claim',
      source_id: recentSession.id,
      snippet: 'legacy session evidence',
      at: '2026-03-20T12:00:00.000Z',
    });

    await setRecencyAnchor(recentSession.id, '2026-03-20T12:00:00.000Z');
    await setRecencyAnchor(staleSession.id, '2026-01-20T12:00:00.000Z');

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    const routedClaim = await findClaimById(recentSession.id);
    const staleClaim = await findClaimById(staleSession.id);
    expect(routedClaim?.memory_type).toBe('knowledge');
    expect(routedClaim?.tombstone).toBe(true);
    expect(routedClaim?.rollback_reason).toContain('promotion_queue');
    expect(staleClaim?.memory_type).toBe('procedure');
    expect(staleClaim?.tombstone).toBe(true);
    expect(staleClaim?.rollback_reason).toContain('stale session claim');

    const conn = await getConnection();
    const queueReader = await conn.runAndReadAll(
      `SELECT id, candidate_hash, proposed_kind, proposed_scope, proposed_memory_type, source_ids, evidence_ids, status
       FROM promotion_queue
       ORDER BY created_at, id`
    );
    const queueRows = queueReader.getRowObjects() as Array<{
      id: string;
      candidate_hash: string;
      proposed_kind: string;
      proposed_scope: string;
      proposed_memory_type: string | null;
      source_ids: string;
      evidence_ids: string;
      status: string;
    }>;

    expect(queueRows).toHaveLength(1);
    expect(queueRows[0]?.candidate_hash).toBe(recentSession.content_hash);
    expect(queueRows[0]?.proposed_kind).toBe('fact');
    expect(queueRows[0]?.proposed_scope).toBe('project');
    expect(queueRows[0]?.proposed_memory_type).toBe('working_state');
    expect(JSON.parse(queueRows[0]?.source_ids ?? '[]')).toEqual([recentSession.id]);
    expect(JSON.parse(queueRows[0]?.evidence_ids ?? '[]')).toEqual(['evd_recent_session']);
    expect(queueRows[0]?.status).toBe('pending');

    expect(report.summary.session_claims_scanned).toBe(2);
    expect(report.summary.session_queue_candidates_created).toBe(1);
    expect(report.summary.session_claims_tombstoned).toBe(2);
    expect(report.session_queue_candidates).toEqual([
      expect.objectContaining({
        claim_id: recentSession.id,
        proposed_scope: 'project',
        proposed_memory_type: 'working_state',
      }),
    ]);
  });

  it('rejects new session upserts and points callers to pce_memory_observe', async () => {
    const policyResult = await applyPolicyOp()();
    expect(E.isRight(policyResult)).toBe(true);

    await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    const result = await handleUpsert({
      text: 'New session memory should use observe',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain("scope 'session'");
    expect(result.structuredContent?.error?.message).toContain('pce_memory_observe');
  });

  it('does not queue session claims already removed from the canonical corpus', async () => {
    const tombstonedSession = await seedClaim({
      text: 'Already tombstoned session memory',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '3'.repeat(64),
    });
    const rolledBackSession = await seedClaim({
      text: 'Already rolled back session memory',
      kind: 'task',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '4'.repeat(64),
    });

    const conn = await getConnection();
    await conn.run(
      `UPDATE claims
       SET tombstone = TRUE,
           tombstone_at = $1::TIMESTAMP,
           rollback_reason = $2
       WHERE id = $3`,
      ['2026-03-23T12:00:00.000Z', 'manual tombstone', tombstonedSession.id]
    );
    await conn.run(
      `INSERT INTO promotion_queue (
         id, source_layer, target_layer, source_ids, distilled_text, candidate_hash,
         proposed_kind, proposed_scope, proposed_boundary_class, proposed_memory_type,
         provenance, evidence_ids, status, created_at, resolved_at, accepted_claim_id, rejected_reason
       ) VALUES (
         $1, $2, $3, $4, $5, $6,
         $7, $8, $9, $10,
         $11, $12, $13, $14, $15, $16, $17
       )`,
      [
        'rbk_session_existing',
        'micro',
        'micro',
        JSON.stringify([rolledBackSession.id]),
        rolledBackSession.text,
        rolledBackSession.content_hash,
        rolledBackSession.kind,
        rolledBackSession.scope,
        rolledBackSession.boundary_class,
        'working_state',
        JSON.stringify({ rollback_of: rolledBackSession.id }),
        JSON.stringify([]),
        'rolled_back',
        '2026-03-23T12:00:00.000Z',
        '2026-03-23T12:00:00.000Z',
        rolledBackSession.id,
        'rolled back before migration',
      ]
    );
    await setRecencyAnchor(tombstonedSession.id, '2026-03-22T12:00:00.000Z');
    await setRecencyAnchor(rolledBackSession.id, '2026-03-22T12:00:00.000Z');

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    const pendingQueueReader = await conn.runAndReadAll(
      `SELECT COUNT(*)::INTEGER AS cnt
       FROM promotion_queue
       WHERE status = 'pending'`
    );
    const pendingQueueRows = pendingQueueReader.getRowObjects() as Array<{ cnt: number }>;

    expect(pendingQueueRows[0]?.cnt).toBe(0);
    expect(report.summary.session_claims_already_tombstoned).toBe(2);
    expect(report.summary.session_queue_candidates_created).toBe(0);
  });

  it('migrates session-only databases using created_at when recency_anchor is missing and reuses existing queue rows', async () => {
    const recentTask = await seedClaim({
      text: 'Recent session task without recency anchor',
      kind: 'task',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'b'.repeat(64),
    });
    const recentFactWithExistingQueue = await seedClaim({
      text: 'Recent session fact already routed once',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'c'.repeat(64),
    });
    const staleSession = await seedClaim({
      text: 'Stale session residue',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'd'.repeat(64),
    });
    const alreadyTombstoned = await seedClaim({
      text: 'Already tombstoned session residue',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'e'.repeat(64),
    });

    await setLegacyClaimState(recentTask.id, {
      createdAt: '2026-03-22T12:00:00.000Z',
      recencyAnchor: null,
    });
    await setLegacyClaimState(recentFactWithExistingQueue.id, {
      createdAt: '2026-03-23T12:00:00.000Z',
      recencyAnchor: null,
    });
    await setLegacyClaimState(staleSession.id, {
      createdAt: '2026-01-20T12:00:00.000Z',
      recencyAnchor: null,
    });
    await setLegacyClaimState(alreadyTombstoned.id, {
      createdAt: '2026-03-20T12:00:00.000Z',
      recencyAnchor: null,
      tombstone: true,
      tombstoneAt: '2026-03-23T12:00:00.000Z',
      rollbackReason: 'already removed',
    });

    const existingCandidateId = `pq_mig_${recentFactWithExistingQueue.id.replace(/^clm_/, '')}`;
    const conn = await getConnection();
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
        existingCandidateId,
        'micro',
        'meso',
        JSON.stringify([recentFactWithExistingQueue.id]),
        recentFactWithExistingQueue.text,
        recentFactWithExistingQueue.content_hash,
        recentFactWithExistingQueue.kind,
        'project',
        recentFactWithExistingQueue.boundary_class,
        'working_state',
        JSON.stringify({ migrated_at: '2026-03-23T12:00:00.000Z' }),
        JSON.stringify([]),
        'v2-memory-type-migration',
        JSON.stringify({ allowed: true }),
        'pending',
        '2026-03-23T12:00:00.000Z',
      ]
    );

    const report = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    const queueReader = await conn.runAndReadAll(
      `SELECT COUNT(*)::INTEGER AS cnt
       FROM promotion_queue
       WHERE status = 'pending'`
    );
    const queueRows = queueReader.getRowObjects() as Array<{ cnt: number }>;

    expect(report.summary.total_claims_scanned).toBe(4);
    expect(report.summary.session_claims_scanned).toBe(4);
    expect(report.summary.session_queue_candidates_created).toBe(1);
    expect(report.summary.session_queue_candidates_existing).toBe(1);
    expect(report.summary.session_claims_tombstoned).toBe(3);
    expect(report.summary.session_claims_already_tombstoned).toBe(1);
    expect(queueRows[0]?.cnt).toBe(2);
    expect((await findClaimById(recentTask.id))?.memory_type).toBe('working_state');
    expect((await findClaimById(staleSession.id))?.memory_type).toBe('knowledge');
    expect((await findClaimById(alreadyTombstoned.id))?.tombstone).toBe(true);
  });

  it('is idempotent when re-run', async () => {
    const durableClaim = await seedClaim({
      text: 'Stable project memory',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '1'.repeat(64),
    });
    const sessionClaim = await seedClaim({
      text: 'Recent branch-local work state',
      kind: 'task',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '2'.repeat(64),
    });
    await setRecencyAnchor(sessionClaim.id, '2026-03-22T12:00:00.000Z');

    const first = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });
    const second = await migrateV2MemoryType({
      now: '2026-03-24T12:00:00.000Z',
    });

    const conn = await getConnection();
    const queueCountReader = await conn.runAndReadAll(
      'SELECT COUNT(*)::INTEGER AS cnt FROM promotion_queue'
    );
    const queueCountRows = queueCountReader.getRowObjects() as Array<{ cnt: number }>;

    expect((await findClaimById(durableClaim.id))?.memory_type).toBe('knowledge');
    expect((await findClaimById(sessionClaim.id))?.memory_type).toBe('working_state');
    expect(queueCountRows[0]?.cnt).toBe(1);

    expect(first.summary.memory_type_backfilled).toBe(2);
    expect(first.summary.session_queue_candidates_created).toBe(1);
    expect(second.summary.memory_type_backfilled).toBe(0);
    expect(second.summary.session_queue_candidates_created).toBe(0);
    expect(second.summary.session_queue_candidates_existing).toBe(0);
    expect(second.summary.session_claims_already_tombstoned).toBe(1);
  });

  it('serializes concurrent migration runs without duplicating queue rows', async () => {
    const sessionClaim = await seedClaim({
      text: 'Concurrent migration should not race',
      kind: 'task',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + 'f'.repeat(64),
    });
    await setRecencyAnchor(sessionClaim.id, '2026-03-22T12:00:00.000Z');

    const reports = await Promise.all([
      migrateV2MemoryType({ now: '2026-03-24T12:00:00.000Z' }),
      migrateV2MemoryType({ now: '2026-03-24T12:00:00.000Z' }),
    ]);

    const conn = await getConnection();
    const queueReader = await conn.runAndReadAll(
      'SELECT COUNT(*)::INTEGER AS cnt FROM promotion_queue WHERE status = $1',
      ['pending']
    );
    const queueRows = queueReader.getRowObjects() as Array<{ cnt: number }>;
    const createdCounts = reports.map((report) => report.summary.session_queue_candidates_created).sort();

    expect(queueRows[0]?.cnt).toBe(1);
    expect(createdCounts).toEqual([0, 1]);
    expect((await findClaimById(sessionClaim.id))?.tombstone).toBe(true);
  });
});

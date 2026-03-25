/**
 * Schema Integrity Tests
 *
 * Validates that:
 * 1. SQL columns match TypeScript types (round-trip correctness)
 * 2. JSON fields (attrs, props, provenance, tags) are properly parsed on read
 * 3. Timestamps are normalized to ISO 8601 strings
 * 4. NULL/undefined handling is consistent
 * 5. Foreign-key-like relationships are maintained
 * 6. content_hash uniqueness is enforced
 * 7. Tombstoned claims are excluded from search paths
 * 8. Migration idempotency
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { upsertClaim, findClaimById, findClaimByContentHash, listClaimsByScope } from '../src/store/claims';
import { upsertEntity, getEntitiesForClaim, linkClaimEntity, findEntityById, findEntityByCanonicalKey, findEntitiesByType, queryEntities } from '../src/store/entities';
import { upsertRelation, findRelationById, getRelationsFromEntity, getRelationsByEvidence, queryRelations } from '../src/store/relations';
import { insertEvidence, getEvidenceForClaim, getEvidenceForClaims } from '../src/store/evidence';
import { insertObservation, findObservationById, findObservationsByIds } from '../src/store/observations';
import { insertPromotionQueueRow, findPromotionQueueRowById, acceptPromotionQueueRow } from '../src/store/promotionQueue';
import { recordFeedback } from '../src/store/feedback';

beforeEach(async () => {
  await resetDbAsync();
  process.env['PCE_DB'] = ':memory:';
  await initDb();
  await initSchema();
});

// ========== APPROACH 1: Schema Integrity ==========

describe('Schema Integrity: SQL ↔ TypeScript round-trip', () => {
  describe('Claim fields round-trip', () => {
    it('all claim fields survive write→read correctly', async () => {
      const provenance = {
        at: '2025-06-01T12:00:00.000Z',
        actor: 'test-user',
        git: { commit: 'abc123', repo: 'test/repo' },
        note: 'test note',
        signed: true,
      };

      const { claim } = await upsertClaim({
        text: 'Test claim text',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:test_hash_001',
        memory_type: 'knowledge',
        status: 'active',
        provenance,
      });

      const found = await findClaimById(claim.id);
      expect(found).toBeDefined();

      // Core fields
      expect(found!.text).toBe('Test claim text');
      expect(found!.kind).toBe('fact');
      expect(found!.scope).toBe('project');
      expect(found!.boundary_class).toBe('internal');
      expect(found!.content_hash).toBe('sha256:test_hash_001');
      expect(found!.memory_type).toBe('knowledge');
      expect(found!.status).toBe('active');

      // Defaults
      expect(found!.utility).toBe(0.0);
      expect(found!.confidence).toBe(0.5);
      expect(found!.retrieval_count).toBe(0);
      expect(found!.tombstone).toBe(false);

      // Provenance JSON round-trip
      expect(found!.provenance).toBeDefined();
      expect(typeof found!.provenance).toBe('object');
      expect(found!.provenance!.at).toBe('2025-06-01T12:00:00.000Z');
      expect(found!.provenance!.actor).toBe('test-user');
      expect(found!.provenance!.git?.commit).toBe('abc123');
      expect(found!.provenance!.note).toBe('test note');
      expect(found!.provenance!.signed).toBe(true);

      // Timestamps are ISO strings (not BigInt or Date objects)
      expect(typeof found!.created_at).toBe('string');
      expect(typeof found!.updated_at).toBe('string');
      expect(typeof found!.recency_anchor).toBe('string');
    });

    it('nullable fields default correctly', async () => {
      const { claim } = await upsertClaim({
        text: 'Minimal claim',
        kind: 'task',
        scope: 'project',
        boundary_class: 'public',
        content_hash: 'sha256:minimal_001',
      });

      const found = await findClaimById(claim.id);
      expect(found!.memory_type).toBeNull();
      expect(found!.last_retrieved_at).toBeNull();
      expect(found!.tombstone_at).toBeNull();
      expect(found!.rollback_reason).toBeNull();
      expect(found!.superseded_by).toBeNull();
    });
  });

  describe('Entity attrs JSON round-trip', () => {
    it('attrs object survives write→read as parsed object, not string', async () => {
      await upsertEntity({
        id: 'ent_test_001',
        type: 'Artifact',
        name: 'Test Library',
        canonical_key: 'test-lib',
        attrs: { version: '2.0', language: 'typescript', nested: { key: 'value' } },
      });

      const found = await findEntityById('ent_test_001');
      expect(found).toBeDefined();
      expect(found!.name).toBe('Test Library');
      expect(found!.canonical_key).toBe('test-lib');

      // BUG CHECK: attrs must be a parsed object, not a JSON string
      expect(typeof found!.attrs).toBe('object');
      expect(found!.attrs).not.toBeNull();
      expect(found!.attrs!.version).toBe('2.0');
      expect(found!.attrs!.language).toBe('typescript');
      expect((found!.attrs!.nested as Record<string, string>).key).toBe('value');
    });

    it('attrs round-trips through all query paths', async () => {
      const attrs = { framework: 'vitest', coverage: true };
      await upsertEntity({
        id: 'ent_query_001',
        type: 'Concept',
        name: 'Testing',
        canonical_key: 'testing',
        attrs,
      });

      // findEntityByCanonicalKey
      const byKey = await findEntityByCanonicalKey('testing');
      expect(typeof byKey!.attrs).toBe('object');
      expect(byKey!.attrs!.framework).toBe('vitest');

      // findEntitiesByType
      const byType = await findEntitiesByType('Concept');
      expect(byType.length).toBeGreaterThan(0);
      expect(typeof byType[0]!.attrs).toBe('object');
      expect(byType[0]!.attrs!.framework).toBe('vitest');

      // queryEntities
      const queried = await queryEntities({ type: 'Concept' });
      expect(queried.length).toBeGreaterThan(0);
      expect(typeof queried[0]!.attrs).toBe('object');
      expect(queried[0]!.attrs!.framework).toBe('vitest');
    });

    it('entity created_at is normalized to ISO string', async () => {
      await upsertEntity({
        id: 'ent_ts_001',
        type: 'Actor',
        name: 'Test Actor',
      });

      const found = await findEntityById('ent_ts_001');
      expect(found).toBeDefined();
      // BUG CHECK: created_at must be a string, not a DuckDB Date/BigInt
      expect(typeof found!.created_at).toBe('string');
      // Verify it's a valid ISO date
      expect(new Date(found!.created_at as string).toISOString()).toBe(found!.created_at);
    });

    it('entity with null attrs returns undefined/null attrs', async () => {
      await upsertEntity({
        id: 'ent_noattrs_001',
        type: 'Event',
        name: 'No Attrs Event',
      });

      const found = await findEntityById('ent_noattrs_001');
      expect(found).toBeDefined();
      // attrs should be null or undefined, not the string "null"
      expect(found!.attrs === null || found!.attrs === undefined).toBe(true);
    });
  });

  describe('Relation props JSON round-trip', () => {
    it('props object survives write→read as parsed object, not string', async () => {
      // Create entities first
      await upsertEntity({ id: 'ent_src', type: 'Artifact', name: 'Source' });
      await upsertEntity({ id: 'ent_dst', type: 'Concept', name: 'Destination' });

      await upsertRelation({
        id: 'rel_test_001',
        src_id: 'ent_src',
        dst_id: 'ent_dst',
        type: 'IMPLEMENTS',
        props: { weight: 0.9, tags: ['core', 'api'], nested: { depth: 1 } },
      });

      const found = await findRelationById('rel_test_001');
      expect(found).toBeDefined();

      // BUG CHECK: props must be a parsed object, not a JSON string
      expect(typeof found!.props).toBe('object');
      expect(found!.props).not.toBeNull();
      expect(found!.props!.weight).toBe(0.9);
      expect(found!.props!.tags).toEqual(['core', 'api']);
      expect((found!.props!.nested as Record<string, number>).depth).toBe(1);
    });

    it('props round-trips through all query paths', async () => {
      await upsertEntity({ id: 'ent_a', type: 'Artifact', name: 'A' });
      await upsertEntity({ id: 'ent_b', type: 'Artifact', name: 'B' });

      const { claim } = await upsertClaim({
        text: 'Evidence claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:evidence_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      await upsertRelation({
        id: 'rel_query_001',
        src_id: 'ent_a',
        dst_id: 'ent_b',
        type: 'USES',
        props: { version: '3.0' },
        evidence_claim_id: claim.id,
      });

      // getRelationsFromEntity
      const fromEntity = await getRelationsFromEntity('ent_a');
      expect(fromEntity.length).toBe(1);
      expect(typeof fromEntity[0]!.props).toBe('object');
      expect(fromEntity[0]!.props!.version).toBe('3.0');

      // getRelationsByEvidence
      const byEvidence = await getRelationsByEvidence(claim.id);
      expect(byEvidence.length).toBe(1);
      expect(typeof byEvidence[0]!.props).toBe('object');

      // queryRelations
      const queried = await queryRelations({ type: 'USES' });
      expect(queried.length).toBe(1);
      expect(typeof queried[0]!.props).toBe('object');
      expect(queried[0]!.props!.version).toBe('3.0');
    });

    it('relation created_at is normalized to ISO string', async () => {
      await upsertEntity({ id: 'ent_r1', type: 'Artifact', name: 'R1' });
      await upsertEntity({ id: 'ent_r2', type: 'Artifact', name: 'R2' });

      await upsertRelation({
        id: 'rel_ts_001',
        src_id: 'ent_r1',
        dst_id: 'ent_r2',
        type: 'DEPENDS_ON',
      });

      const found = await findRelationById('rel_ts_001');
      expect(found).toBeDefined();
      // BUG CHECK: created_at must be a string, not a DuckDB Date/BigInt
      expect(typeof found!.created_at).toBe('string');
      expect(new Date(found!.created_at as string).toISOString()).toBe(found!.created_at);
    });
  });

  describe('Evidence fields round-trip', () => {
    it('evidence at field maps correctly from recorded_at', async () => {
      const { claim } = await upsertClaim({
        text: 'Evidence test',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:ev_test_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      const evidence = await insertEvidence({
        id: 'ev_001',
        claim_id: claim.id,
        source_type: 'code',
        source_id: 'file.ts:42',
        snippet: 'const x = 1;',
        at: '2025-06-15T10:00:00.000Z',
      });

      expect(evidence.at).toBeDefined();
      expect(typeof evidence.at).toBe('string');

      const evidences = await getEvidenceForClaim(claim.id);
      expect(evidences.length).toBe(1);
      expect(typeof evidences[0]!.at).toBe('string');

      // Batch query
      const batchMap = await getEvidenceForClaims([claim.id]);
      const batchEvs = batchMap.get(claim.id);
      expect(batchEvs).toBeDefined();
      expect(batchEvs!.length).toBe(1);
      expect(typeof batchEvs![0]!.at).toBe('string');
    });
  });

  describe('Observation tags JSON round-trip', () => {
    it('tags array survives write→read through findObservationById', async () => {
      const expiresAt = new Date(Date.now() + 86400000).toISOString();
      await insertObservation({
        id: 'obs_tags_001',
        source_type: 'chat',
        content: 'Test observation with tags',
        boundary_class: 'internal',
        content_digest: 'sha256:obs_tags_digest',
        content_length: 26,
        tags: ['bug', 'critical', 'auth'],
        expires_at: expiresAt,
      });

      const found = await findObservationById('obs_tags_001');
      expect(found).toBeDefined();

      // BUG CHECK: tags should be a parsed array, not a JSON string
      const tags = found!.tags;
      expect(Array.isArray(tags)).toBe(true);
      expect(tags).toEqual(['bug', 'critical', 'auth']);
    });

    it('tags array survives write→read through findObservationsByIds', async () => {
      const expiresAt = new Date(Date.now() + 86400000).toISOString();
      await insertObservation({
        id: 'obs_tags_002',
        source_type: 'tool',
        content: 'Another observation',
        boundary_class: 'internal',
        content_digest: 'sha256:obs_tags_digest_002',
        content_length: 19,
        tags: ['debug', 'perf'],
        expires_at: expiresAt,
      });

      const found = await findObservationsByIds(['obs_tags_002']);
      expect(found.length).toBe(1);

      // BUG CHECK: tags should be parsed
      const tags = found[0]!.tags;
      expect(Array.isArray(tags)).toBe(true);
      expect(tags).toEqual(['debug', 'perf']);
    });

    it('observation timestamps are normalized', async () => {
      const expiresAt = new Date(Date.now() + 86400000).toISOString();
      await insertObservation({
        id: 'obs_ts_001',
        source_type: 'system',
        content: 'Timestamp test',
        boundary_class: 'public',
        content_digest: 'sha256:obs_ts_digest',
        content_length: 14,
        expires_at: expiresAt,
      });

      const found = await findObservationById('obs_ts_001');
      expect(found).toBeDefined();
      expect(typeof found!.created_at).toBe('string');
      expect(typeof found!.expires_at).toBe('string');
    });
  });
});

// ========== APPROACH 2: Migration Safety ==========

describe('Migration Safety', () => {
  it('migrations are idempotent (running initSchema twice)', async () => {
    // First init already ran in beforeEach
    // Run again - should not throw
    await initSchema();

    // Verify schema is intact
    const { claim } = await upsertClaim({
      text: 'Post double-init claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:double_init_001',
      provenance: { at: '2025-01-01T00:00:00Z' },
    });
    expect(claim.id).toBeDefined();
  });

  it('migrations work on empty DB', async () => {
    // beforeEach already tests this - verify all tables exist
    const conn = await getConnection();

    const tables = [
      'claims', 'active_contexts', 'active_context_items', 'promotion_queue',
      'logs', 'feedback', 'rate_state', 'critic', 'policies',
      'embedding_cache', 'claim_vectors', 'claim_links',
      'entities', 'claim_entities', 'relations', 'evidence', 'observations',
    ];

    for (const table of tables) {
      const reader = await conn.runAndReadAll(
        "SELECT COUNT(*)::INTEGER AS cnt FROM information_schema.tables WHERE table_name = $1",
        [table]
      );
      const rows = reader.getRowObjects() as Array<{ cnt: number }>;
      expect(rows[0]!.cnt, `Table '${table}' should exist`).toBe(1);
    }
  });

  it('migrations work with data already present', async () => {
    // Insert data
    await upsertClaim({
      text: 'Pre-migration claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:pre_mig_001',
      provenance: { at: '2025-01-01T00:00:00Z' },
    });

    // Run migrations again
    await initSchema();

    // Data should survive
    const found = await findClaimByContentHash('sha256:pre_mig_001');
    expect(found).toBeDefined();
    expect(found!.text).toBe('Pre-migration claim');
  });
});

// ========== APPROACH 3: Data Integrity ==========

describe('Data Integrity', () => {
  describe('content_hash uniqueness', () => {
    it('duplicate content_hash returns existing claim (idempotent upsert)', async () => {
      const { claim: first, isNew: isNew1 } = await upsertClaim({
        text: 'Unique text',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:unique_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });
      expect(isNew1).toBe(true);

      const { claim: second, isNew: isNew2 } = await upsertClaim({
        text: 'Unique text',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:unique_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });
      expect(isNew2).toBe(false);
      expect(second.id).toBe(first.id);
    });

    it('content_hash collision with different text throws', async () => {
      await upsertClaim({
        text: 'Original text',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:collision_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      await expect(
        upsertClaim({
          text: 'Different text',
          kind: 'fact',
          scope: 'project',
          boundary_class: 'internal',
          content_hash: 'sha256:collision_001',
          provenance: { at: '2025-01-01T00:00:00Z' },
        })
      ).rejects.toThrow('content_hash collision');
    });
  });

  describe('Entity-Claim linkage', () => {
    it('entities linked to claim are retrievable', async () => {
      const { claim } = await upsertClaim({
        text: 'Linked claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:linked_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      await upsertEntity({ id: 'ent_linked_1', type: 'Artifact', name: 'Library A' });
      await upsertEntity({ id: 'ent_linked_2', type: 'Concept', name: 'Pattern B' });

      await linkClaimEntity(claim.id, 'ent_linked_1');
      await linkClaimEntity(claim.id, 'ent_linked_2');

      const entities = await getEntitiesForClaim(claim.id);
      expect(entities.length).toBe(2);
      const entityIds = entities.map((e) => e.id).sort();
      expect(entityIds).toEqual(['ent_linked_1', 'ent_linked_2']);
    });

    it('queryEntities with claim_id filter works', async () => {
      const { claim } = await upsertClaim({
        text: 'Query test claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:query_ent_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      await upsertEntity({ id: 'ent_q1', type: 'Artifact', name: 'Q1' });
      await upsertEntity({ id: 'ent_q2', type: 'Artifact', name: 'Q2' });
      await linkClaimEntity(claim.id, 'ent_q1');

      const linked = await queryEntities({ claim_id: claim.id });
      expect(linked.length).toBe(1);
      expect(linked[0]!.id).toBe('ent_q1');
    });
  });

  describe('Tombstone exclusion', () => {
    it('tombstoned claims are excluded from findClaimByContentHash', async () => {
      const { claim } = await upsertClaim({
        text: 'Will be tombstoned',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:tomb_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      // Tombstone the claim
      const conn = await getConnection();
      await conn.run(
        "UPDATE claims SET tombstone = TRUE, tombstone_at = CURRENT_TIMESTAMP WHERE id = $1",
        [claim.id]
      );

      const found = await findClaimByContentHash('sha256:tomb_001');
      expect(found).toBeUndefined();
    });

    it('tombstoned claims are excluded from listClaimsByScope', async () => {
      await upsertClaim({
        text: 'Active claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:active_list_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      const { claim: tombClaim } = await upsertClaim({
        text: 'Tombstoned claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:tomb_list_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      const conn = await getConnection();
      await conn.run(
        "UPDATE claims SET tombstone = TRUE WHERE id = $1",
        [tombClaim.id]
      );

      const claims = await listClaimsByScope(['project'], 100);
      expect(claims.length).toBe(1);
      expect(claims[0]!.content_hash).toBe('sha256:active_list_001');
    });

    it('rolled-back claims (via promotion_queue) are excluded from search', async () => {
      const { claim } = await upsertClaim({
        text: 'Will be rolled back via PQ',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:rollback_pq_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      // Create a rolled_back promotion_queue entry pointing to this claim
      await insertPromotionQueueRow({
        id: 'pq_rb_001',
        source_layer: 'micro',
        target_layer: 'meso',
        source_ids: '["obs_1"]',
        distilled_text: 'Distilled text',
        candidate_hash: 'sha256:cand_001',
        proposed_kind: 'fact',
        proposed_scope: 'project',
        proposed_boundary_class: 'internal',
        provenance: '{}',
        evidence_ids: '[]',
        status: 'rolled_back',
        created_at: new Date().toISOString(),
        accepted_claim_id: claim.id,
      });

      const found = await findClaimByContentHash('sha256:rollback_pq_001');
      expect(found).toBeUndefined();
    });
  });

  describe('Promotion queue lifecycle', () => {
    it('insert → find → accept lifecycle', async () => {
      const pqId = 'pq_lifecycle_001';
      const created = await insertPromotionQueueRow({
        id: pqId,
        source_layer: 'micro',
        target_layer: 'meso',
        source_ids: '["obs_a","obs_b"]',
        distilled_text: 'Distilled knowledge',
        candidate_hash: 'sha256:cand_lifecycle_001',
        proposed_kind: 'fact',
        proposed_scope: 'project',
        proposed_boundary_class: 'internal',
        proposed_memory_type: 'knowledge',
        provenance: JSON.stringify({ at: '2025-06-01T00:00:00Z', actor: 'claude' }),
        evidence_ids: '["ev_1"]',
        created_at: new Date().toISOString(),
      });

      expect(created.id).toBe(pqId);
      expect(created.status).toBe('pending');
      expect(created.proposed_memory_type).toBe('knowledge');

      // Find
      const found = await findPromotionQueueRowById(pqId);
      expect(found).toBeDefined();
      expect(found!.distilled_text).toBe('Distilled knowledge');

      // Accept
      const { claim } = await upsertClaim({
        text: 'Distilled knowledge',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:promoted_001',
        memory_type: 'knowledge',
        provenance: { at: '2025-06-01T00:00:00Z' },
      });

      const accepted = await acceptPromotionQueueRow(pqId, {
        accepted_claim_id: claim.id,
        resolved_at: new Date().toISOString(),
      });
      expect(accepted).toBe(true);

      // Verify status changed
      const afterAccept = await findPromotionQueueRowById(pqId);
      expect(afterAccept!.status).toBe('accepted');
      expect(afterAccept!.accepted_claim_id).toBe(claim.id);
    });
  });

  describe('Observation expiry and scrub', () => {
    it('expired observation content is scrubbed by GC', async () => {
      // Insert already-expired observation
      const pastExpiry = new Date(Date.now() - 86400000).toISOString();
      await insertObservation({
        id: 'obs_expired_001',
        source_type: 'chat',
        content: 'Sensitive content that should be scrubbed',
        boundary_class: 'pii',
        content_digest: 'sha256:expired_digest',
        content_length: 40,
        actor: 'user@example.com',
        tags: ['sensitive'],
        expires_at: pastExpiry,
      });

      // Import and run GC
      const { gcExpiredObservations } = await import('../src/store/observations');
      await gcExpiredObservations('scrub');

      const found = await findObservationById('obs_expired_001');
      expect(found).toBeDefined();
      // Content fields should be NULL after scrub
      expect(found!.content).toBeNull();
      expect(found!.actor).toBeNull();
      expect(found!.source_id).toBeNull();
      // Metadata should survive
      expect(found!.content_digest).toBe('sha256:expired_digest');
      expect(found!.content_length).toBe(40);
    });
  });

  describe('Feedback updates claim metrics', () => {
    it('helpful feedback increases utility and confidence', async () => {
      const { claim } = await upsertClaim({
        text: 'Feedback test claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:feedback_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      const initialClaim = await findClaimById(claim.id);
      const initialUtility = initialClaim!.utility;
      const initialConfidence = initialClaim!.confidence;

      await recordFeedback({ claim_id: claim.id, signal: 'helpful' });

      const updatedClaim = await findClaimById(claim.id);
      expect(updatedClaim!.utility).toBeGreaterThan(initialUtility);
      expect(updatedClaim!.confidence).toBeGreaterThan(initialConfidence);
    });

    it('harmful feedback decreases utility and confidence', async () => {
      const { claim } = await upsertClaim({
        text: 'Harmful feedback test',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:harmful_fb_001',
        provenance: { at: '2025-01-01T00:00:00Z' },
      });

      await recordFeedback({ claim_id: claim.id, signal: 'harmful' });

      const updated = await findClaimById(claim.id);
      expect(updated!.utility).toBeLessThan(0);
      expect(updated!.confidence).toBeLessThan(0.5);
    });
  });
});

// ========== APPROACH 4: Type Safety Audit (runtime checks) ==========

describe('Type Safety: enum consistency', () => {
  it('all CLAIM_KINDS can be upserted', async () => {
    const kinds = ['fact', 'preference', 'task', 'policy_hint'] as const;
    for (const kind of kinds) {
      const { claim } = await upsertClaim({
        text: `Kind test: ${kind}`,
        kind,
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:kind_${kind}`,
        provenance: { at: '2025-01-01T00:00:00Z' },
      });
      expect(claim.kind).toBe(kind);
    }
  });

  it('all MEMORY_TYPES can be upserted', async () => {
    const types = ['evidence', 'working_state', 'knowledge', 'procedure', 'norm'] as const;
    for (const memType of types) {
      const { claim } = await upsertClaim({
        text: `Memory type test: ${memType}`,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:memtype_${memType}`,
        memory_type: memType,
        provenance: { at: '2025-01-01T00:00:00Z' },
      });
      expect(claim.memory_type).toBe(memType);
    }
  });

  it('all ENTITY_TYPES can be created', async () => {
    const types = ['Actor', 'Artifact', 'Event', 'Concept'] as const;
    for (const entityType of types) {
      const entity = await upsertEntity({
        id: `ent_type_${entityType.toLowerCase()}`,
        type: entityType,
        name: `Test ${entityType}`,
      });
      expect(entity.type).toBe(entityType);
    }
  });

  it('all FEEDBACK_SIGNALS can be recorded', async () => {
    const { claim } = await upsertClaim({
      text: 'Signal test claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:signal_test_001',
      provenance: { at: '2025-01-01T00:00:00Z' },
    });

    const signals = ['helpful', 'harmful', 'outdated', 'duplicate', 'completed'] as const;
    for (const signal of signals) {
      const result = await recordFeedback({ claim_id: claim.id, signal });
      expect(result.id).toBeDefined();
    }
  });
});

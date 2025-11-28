/**
 * Graph Memory Unit Tests
 * entities.ts, relations.ts, evidence.ts のユニットテスト
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import {
  upsertEntity,
  linkClaimEntity,
  getEntitiesForClaim,
  findEntitiesByType,
  findEntityByCanonicalKey,
} from '../src/store/entities';
import {
  upsertRelation,
  getRelationsFromEntity,
  getRelationsToEntity,
  getRelationsByEvidence,
  findRelationsByType,
} from '../src/store/relations';
import {
  insertEvidence,
  getEvidenceForClaim,
  getEvidenceForClaims,
  findEvidenceBySourceType,
} from '../src/store/evidence';
import { upsertClaim } from '../src/store/claims';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

// ========== Entity Tests ==========

describe('Entity Store', () => {
  describe('upsertEntity', () => {
    it('creates a new entity with all fields', async () => {
      const entity = await upsertEntity({
        id: 'ent_001',
        type: 'Actor',
        name: 'John Doe',
        canonical_key: 'john.doe@example.com',
        attrs: { role: 'developer' },
      });

      expect(entity.id).toBe('ent_001');
      expect(entity.type).toBe('Actor');
      expect(entity.name).toBe('John Doe');
      expect(entity.canonical_key).toBe('john.doe@example.com');
      expect(entity.created_at).toBeDefined();
    });

    it('returns existing entity on duplicate id (idempotent)', async () => {
      const first = await upsertEntity({
        id: 'ent_dup',
        type: 'Artifact',
        name: 'Original',
      });

      const second = await upsertEntity({
        id: 'ent_dup',
        type: 'Event',
        name: 'Modified',
      });

      expect(second.id).toBe(first.id);
      expect(second.name).toBe('Original'); // 変更されない
      expect(second.type).toBe('Artifact'); // 変更されない
    });

    it('creates entity without optional fields', async () => {
      const entity = await upsertEntity({
        id: 'ent_minimal',
        type: 'Concept',
        name: 'Abstract Idea',
      });

      expect(entity.id).toBe('ent_minimal');
      expect(entity.canonical_key).toBeNull();
      expect(entity.attrs).toBeNull();
    });
  });

  describe('linkClaimEntity', () => {
    it('links claim to entity', async () => {
      // Setup
      const { claim } = await upsertClaim({
        text: 'Test claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:link_test',
      });
      await upsertEntity({
        id: 'ent_link',
        type: 'Actor',
        name: 'Test Actor',
      });

      // Link
      await linkClaimEntity(claim.id, 'ent_link');

      // Verify
      const entities = await getEntitiesForClaim(claim.id);
      expect(entities).toHaveLength(1);
      expect(entities[0]!.id).toBe('ent_link');
    });

    it('handles duplicate links gracefully (ON CONFLICT DO NOTHING)', async () => {
      const { claim } = await upsertClaim({
        text: 'Test claim 2',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'sha256:link_dup',
      });
      await upsertEntity({
        id: 'ent_link2',
        type: 'Artifact',
        name: 'Test Artifact',
      });

      // 2回リンク（重複）
      await linkClaimEntity(claim.id, 'ent_link2');
      await linkClaimEntity(claim.id, 'ent_link2');

      const entities = await getEntitiesForClaim(claim.id);
      expect(entities).toHaveLength(1);
    });
  });

  describe('findEntitiesByType', () => {
    it('returns entities filtered by type', async () => {
      await upsertEntity({ id: 'actor1', type: 'Actor', name: 'Actor 1' });
      await upsertEntity({ id: 'actor2', type: 'Actor', name: 'Actor 2' });
      await upsertEntity({ id: 'artifact1', type: 'Artifact', name: 'Artifact 1' });

      const actors = await findEntitiesByType('Actor');
      expect(actors).toHaveLength(2);
      expect(actors.every((e) => e.type === 'Actor')).toBe(true);
    });

    it('returns empty array when no entities match', async () => {
      const events = await findEntitiesByType('Event');
      expect(events).toHaveLength(0);
    });
  });

  describe('findEntityByCanonicalKey', () => {
    it('finds entity by canonical_key', async () => {
      await upsertEntity({
        id: 'ent_ck',
        type: 'Actor',
        name: 'Keyed Actor',
        canonical_key: 'unique-key-123',
      });

      const found = await findEntityByCanonicalKey('unique-key-123');
      expect(found).toBeDefined();
      expect(found?.id).toBe('ent_ck');
    });

    it('returns undefined when not found', async () => {
      const notFound = await findEntityByCanonicalKey('nonexistent');
      expect(notFound).toBeUndefined();
    });
  });
});

// ========== Relation Tests ==========

describe('Relation Store', () => {
  describe('upsertRelation', () => {
    it('creates a new relation with all fields', async () => {
      const relation = await upsertRelation({
        id: 'rel_001',
        src_id: 'ent_a',
        dst_id: 'ent_b',
        type: 'KNOWS',
        props: { since: '2024-01' },
        evidence_claim_id: 'clm_123',
      });

      expect(relation.id).toBe('rel_001');
      expect(relation.src_id).toBe('ent_a');
      expect(relation.dst_id).toBe('ent_b');
      expect(relation.type).toBe('KNOWS');
      expect(relation.evidence_claim_id).toBe('clm_123');
    });

    it('returns existing relation on duplicate id (idempotent)', async () => {
      const first = await upsertRelation({
        id: 'rel_dup',
        src_id: 'a',
        dst_id: 'b',
        type: 'ORIGINAL',
      });

      const second = await upsertRelation({
        id: 'rel_dup',
        src_id: 'x',
        dst_id: 'y',
        type: 'MODIFIED',
      });

      expect(second.id).toBe(first.id);
      expect(second.type).toBe('ORIGINAL');
    });
  });

  describe('getRelationsFromEntity', () => {
    it('returns outbound relations', async () => {
      await upsertRelation({ id: 'r1', src_id: 'src', dst_id: 'dst1', type: 'LINK' });
      await upsertRelation({ id: 'r2', src_id: 'src', dst_id: 'dst2', type: 'LINK' });
      await upsertRelation({ id: 'r3', src_id: 'other', dst_id: 'dst3', type: 'LINK' });

      const relations = await getRelationsFromEntity('src');
      expect(relations).toHaveLength(2);
    });
  });

  describe('getRelationsToEntity', () => {
    it('returns inbound relations', async () => {
      await upsertRelation({ id: 'r4', src_id: 'a', dst_id: 'target', type: 'POINTS' });
      await upsertRelation({ id: 'r5', src_id: 'b', dst_id: 'target', type: 'POINTS' });

      const relations = await getRelationsToEntity('target');
      expect(relations).toHaveLength(2);
    });
  });

  describe('getRelationsByEvidence', () => {
    it('returns relations with specific evidence_claim_id', async () => {
      await upsertRelation({
        id: 'r6',
        src_id: 'x',
        dst_id: 'y',
        type: 'T',
        evidence_claim_id: 'clm_ev',
      });
      await upsertRelation({
        id: 'r7',
        src_id: 'x',
        dst_id: 'z',
        type: 'T',
        evidence_claim_id: 'clm_other',
      });

      const relations = await getRelationsByEvidence('clm_ev');
      expect(relations).toHaveLength(1);
      expect(relations[0]!.id).toBe('r6');
    });
  });

  describe('findRelationsByType', () => {
    it('returns relations filtered by type', async () => {
      await upsertRelation({ id: 'r8', src_id: 'a', dst_id: 'b', type: 'FRIEND' });
      await upsertRelation({ id: 'r9', src_id: 'c', dst_id: 'd', type: 'FRIEND' });
      await upsertRelation({ id: 'r10', src_id: 'e', dst_id: 'f', type: 'ENEMY' });

      const friends = await findRelationsByType('FRIEND');
      expect(friends).toHaveLength(2);
    });
  });
});

// ========== Evidence Tests ==========

describe('Evidence Store', () => {
  describe('insertEvidence', () => {
    it('creates evidence with all fields', async () => {
      const evidence = await insertEvidence({
        id: 'ev_001',
        claim_id: 'clm_test',
        source_type: 'git_commit',
        source_id: 'abc123',
        snippet: 'Changed line 42',
        at: '2024-01-15T10:00:00Z',
      });

      expect(evidence.id).toBe('ev_001');
      expect(evidence.claim_id).toBe('clm_test');
      expect(evidence.source_type).toBe('git_commit');
      expect(evidence.source_id).toBe('abc123');
      expect(evidence.snippet).toBe('Changed line 42');
    });

    it('creates evidence with minimal fields', async () => {
      const evidence = await insertEvidence({
        id: 'ev_minimal',
        claim_id: 'clm_test2',
      });

      expect(evidence.id).toBe('ev_minimal');
      expect(evidence.claim_id).toBe('clm_test2');
      expect(evidence.at).toBeDefined(); // DEFAULT CURRENT_TIMESTAMP
    });
  });

  describe('getEvidenceForClaim', () => {
    it('returns evidences for a claim ordered by recorded_at DESC', async () => {
      await insertEvidence({
        id: 'ev_old',
        claim_id: 'clm_ev_test',
        at: '2024-01-01T00:00:00Z',
      });
      await insertEvidence({
        id: 'ev_new',
        claim_id: 'clm_ev_test',
        at: '2024-06-01T00:00:00Z',
      });

      const evidences = await getEvidenceForClaim('clm_ev_test');
      expect(evidences).toHaveLength(2);
      expect(evidences[0]!.id).toBe('ev_new'); // 新しい方が先
    });

    it('returns empty array for non-existent claim', async () => {
      const evidences = await getEvidenceForClaim('nonexistent');
      expect(evidences).toHaveLength(0);
    });
  });

  describe('getEvidenceForClaims (batch)', () => {
    it('returns evidences grouped by claim_id', async () => {
      await insertEvidence({ id: 'ev_a1', claim_id: 'clm_a' });
      await insertEvidence({ id: 'ev_a2', claim_id: 'clm_a' });
      await insertEvidence({ id: 'ev_b1', claim_id: 'clm_b' });

      const map = await getEvidenceForClaims(['clm_a', 'clm_b', 'clm_c']);
      expect(map.get('clm_a')).toHaveLength(2);
      expect(map.get('clm_b')).toHaveLength(1);
      expect(map.get('clm_c')).toBeUndefined(); // 存在しない
    });

    it('returns empty map for empty input', async () => {
      const map = await getEvidenceForClaims([]);
      expect(map.size).toBe(0);
    });
  });

  describe('findEvidenceBySourceType', () => {
    it('returns evidences filtered by source_type', async () => {
      await insertEvidence({ id: 'ev_git1', claim_id: 'c1', source_type: 'git' });
      await insertEvidence({ id: 'ev_git2', claim_id: 'c2', source_type: 'git' });
      await insertEvidence({ id: 'ev_url', claim_id: 'c3', source_type: 'url' });

      const gitEvidences = await findEvidenceBySourceType('git');
      expect(gitEvidences).toHaveLength(2);
    });
  });
});

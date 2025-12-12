/**
 * Unit Tests for Conflict Detection (Issue #18 Phase 3)
 *
 * 衝突検出の具体的なシナリオをテスト
 */
import { describe, it, expect } from 'vitest';
import {
  detectClaimConflict,
  detectEntityConflict,
  detectRelationConflict,
  createMissingReferenceConflict,
  createEmptyConflictReport,
  addConflict,
} from '../src/sync/conflict.js';
import type { ClaimExport, EntityExport, RelationExport } from '../src/sync/schemas.js';

describe('detectClaimConflict', () => {
  const baseClaim: ClaimExport = {
    text: 'Test claim',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'public',
    content_hash: 'sha256:' + 'a'.repeat(64),
  };

  it('既存Claimなしの場合はconflictなし', () => {
    const conflict = detectClaimConflict(undefined, baseClaim);
    expect(conflict).toBeNull();
  });

  it('同じboundary_classの場合はconflictなし', () => {
    const conflict = detectClaimConflict({ boundary_class: 'public' }, baseClaim);
    expect(conflict).toBeNull();
  });

  it('格下げ（internal → public）の場合はconflictなし', () => {
    const conflict = detectClaimConflict({ boundary_class: 'internal' }, baseClaim);
    expect(conflict).toBeNull();
  });

  it('格上げ（public → internal）の場合はboundary_upgrade conflict', () => {
    const conflict = detectClaimConflict({ boundary_class: 'public' }, {
      ...baseClaim,
      boundary_class: 'internal',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('boundary_upgrade');
    expect(conflict?.resolution).toBe('auto_resolved');
  });

  it('格上げ（internal → pii）の場合はboundary_upgrade conflict', () => {
    const conflict = detectClaimConflict({ boundary_class: 'internal' }, {
      ...baseClaim,
      boundary_class: 'pii',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('boundary_upgrade');
    expect(conflict?.localValue).toBe('internal');
    expect(conflict?.remoteValue).toBe('pii');
  });

  it('格上げ（public → secret）の場合はboundary_upgrade conflict', () => {
    const conflict = detectClaimConflict({ boundary_class: 'public' }, {
      ...baseClaim,
      boundary_class: 'secret',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('boundary_upgrade');
    expect(conflict?.message).toContain('public');
    expect(conflict?.message).toContain('secret');
  });
});

describe('detectEntityConflict', () => {
  const baseEntity: EntityExport = {
    id: 'ent_test',
    type: 'Actor',
    name: 'Test Entity',
  };

  it('既存Entityなしの場合はconflictなし', () => {
    const conflict = detectEntityConflict(undefined, baseEntity);
    expect(conflict).toBeNull();
  });

  it('同一内容の場合はconflictなし', () => {
    const conflict = detectEntityConflict(baseEntity, baseEntity);
    expect(conflict).toBeNull();
  });

  it('nameが異なる場合はentity_content_diff conflict', () => {
    const conflict = detectEntityConflict(baseEntity, {
      ...baseEntity,
      name: 'Different Name',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('entity_content_diff');
    expect(conflict?.resolution).toBe('skipped');
    expect(conflict?.id).toBe('ent_test');
  });

  it('typeが異なる場合はentity_content_diff conflict', () => {
    const conflict = detectEntityConflict(baseEntity, {
      ...baseEntity,
      type: 'Artifact',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('entity_content_diff');
  });

  it('attrsの有無が異なる場合はentity_content_diff conflict', () => {
    const conflict = detectEntityConflict(baseEntity, {
      ...baseEntity,
      attrs: { key: 'value' },
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('entity_content_diff');
  });

  it('canonical_keyが異なる場合はentity_content_diff conflict', () => {
    const withKey: EntityExport = { ...baseEntity, canonical_key: 'key1' };
    const conflict = detectEntityConflict(withKey, {
      ...baseEntity,
      canonical_key: 'key2',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('entity_content_diff');
  });
});

describe('detectRelationConflict', () => {
  const baseRelation: RelationExport = {
    id: 'rel_test',
    src_id: 'ent_src',
    dst_id: 'ent_dst',
    type: 'KNOWS',
  };

  it('既存Relationなしの場合はconflictなし', () => {
    const conflict = detectRelationConflict(undefined, baseRelation);
    expect(conflict).toBeNull();
  });

  it('同一内容の場合はconflictなし', () => {
    const conflict = detectRelationConflict(baseRelation, baseRelation);
    expect(conflict).toBeNull();
  });

  it('src_idが異なる場合はrelation_content_diff conflict', () => {
    const conflict = detectRelationConflict(baseRelation, {
      ...baseRelation,
      src_id: 'ent_other',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('relation_content_diff');
    expect(conflict?.resolution).toBe('skipped');
  });

  it('dst_idが異なる場合はrelation_content_diff conflict', () => {
    const conflict = detectRelationConflict(baseRelation, {
      ...baseRelation,
      dst_id: 'ent_other',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('relation_content_diff');
  });

  it('typeが異なる場合はrelation_content_diff conflict', () => {
    const conflict = detectRelationConflict(baseRelation, {
      ...baseRelation,
      type: 'USES',
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('relation_content_diff');
  });

  it('propsの有無が異なる場合はrelation_content_diff conflict', () => {
    const conflict = detectRelationConflict(baseRelation, {
      ...baseRelation,
      props: { weight: 1 },
    });
    expect(conflict).not.toBeNull();
    expect(conflict?.type).toBe('relation_content_diff');
  });
});

describe('createMissingReferenceConflict', () => {
  it('missing_reference conflictを作成する（単一の欠損ID）', () => {
    const conflict = createMissingReferenceConflict('rel_123', ['ent_missing']);
    expect(conflict.type).toBe('missing_reference');
    expect(conflict.id).toBe('rel_123');
    expect(conflict.resolution).toBe('skipped');
    expect(conflict.message).toContain('ent_missing');
  });

  it('missing_reference conflictを作成する（複数の欠損ID）', () => {
    const conflict = createMissingReferenceConflict('rel_123', ['ent_src', 'ent_dst']);
    expect(conflict.type).toBe('missing_reference');
    expect(conflict.id).toBe('rel_123');
    expect(conflict.resolution).toBe('skipped');
    expect(conflict.message).toContain('ent_src');
    expect(conflict.message).toContain('ent_dst');
  });
});

describe('ConflictReport', () => {
  it('空のレポートを作成できる', () => {
    const report = createEmptyConflictReport();
    expect(report.conflicts).toHaveLength(0);
    expect(report.autoResolved).toBe(0);
    expect(report.skipped).toBe(0);
  });

  it('auto_resolved conflictを追加するとカウントが増加', () => {
    let report = createEmptyConflictReport();
    report = addConflict(report, {
      type: 'boundary_upgrade',
      id: 'test',
      resolution: 'auto_resolved',
      message: 'test',
    });
    expect(report.conflicts).toHaveLength(1);
    expect(report.autoResolved).toBe(1);
    expect(report.skipped).toBe(0);
  });

  it('skipped conflictを追加するとカウントが増加', () => {
    let report = createEmptyConflictReport();
    report = addConflict(report, {
      type: 'entity_content_diff',
      id: 'test',
      resolution: 'skipped',
      message: 'test',
    });
    expect(report.conflicts).toHaveLength(1);
    expect(report.autoResolved).toBe(0);
    expect(report.skipped).toBe(1);
  });

  it('複数のconflictを追加できる', () => {
    let report = createEmptyConflictReport();
    report = addConflict(report, {
      type: 'boundary_upgrade',
      id: 'test1',
      resolution: 'auto_resolved',
      message: 'test1',
    });
    report = addConflict(report, {
      type: 'entity_content_diff',
      id: 'test2',
      resolution: 'skipped',
      message: 'test2',
    });
    report = addConflict(report, {
      type: 'missing_reference',
      id: 'test3',
      resolution: 'skipped',
      message: 'test3',
    });
    expect(report.conflicts).toHaveLength(3);
    expect(report.autoResolved).toBe(1);
    expect(report.skipped).toBe(2);
  });
});

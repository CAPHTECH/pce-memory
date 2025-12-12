/**
 * 同期バリデーションテスト (Issue #18)
 */
import { describe, it, expect } from 'vitest';
import * as E from 'fp-ts/Either';
import { computeContentHash } from '@pce/embeddings';
import {
  validateContentHashMatch,
  validateClaimExport,
  validateEntityExport,
  validateRelationExport,
  validateManifest,
} from '../src/sync/validation.js';

describe('validateContentHashMatch', () => {
  it('content_hashとテキストが一致する場合はRight', () => {
    const text = 'テスト用テキスト';
    const hash = `sha256:${computeContentHash(text)}`;
    const result = validateContentHashMatch(text, hash, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('content_hashとテキストが一致しない場合はLeft', () => {
    const text = 'テスト用テキスト';
    const wrongHash = 'sha256:0000000000000000000000000000000000000000000000000000000000000000';
    const result = validateContentHashMatch(text, wrongHash, 'test.json');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.error).toContain('Content hash mismatch');
    }
  });
});

describe('validateClaimExport', () => {
  const validText = 'テスト用テキスト';
  const validHash = `sha256:${computeContentHash(validText)}`;

  const validClaim = {
    text: validText,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: validHash,
  };

  it('有効なClaimはRight', () => {
    const result = validateClaimExport(validClaim, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('provenanceを含む有効なClaimはRight', () => {
    const claimWithProvenance = {
      ...validClaim,
      provenance: {
        at: '2025-12-12T10:00:00Z',
        actor: 'claude',
        note: 'テスト用',
      },
    };
    const result = validateClaimExport(claimWithProvenance, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('kindが無効な場合はLeft', () => {
    const invalidClaim = { ...validClaim, kind: 'invalid_kind' };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });

  it('scopeが無効な場合はLeft', () => {
    const invalidClaim = { ...validClaim, scope: 'invalid_scope' };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });

  it('boundary_classが無効な場合はLeft', () => {
    const invalidClaim = { ...validClaim, boundary_class: 'invalid' };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });

  it('content_hash形式が無効な場合はLeft', () => {
    const invalidClaim = { ...validClaim, content_hash: 'invalid_hash' };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });

  it('content_hashとテキストが不一致の場合はLeft', () => {
    const wrongHash = 'sha256:0000000000000000000000000000000000000000000000000000000000000000';
    const invalidClaim = { ...validClaim, content_hash: wrongHash };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.error).toContain('Content hash mismatch');
    }
  });

  it('textが空の場合はLeft', () => {
    const emptyHash = `sha256:${computeContentHash('')}`;
    const invalidClaim = { ...validClaim, text: '', content_hash: emptyHash };
    const result = validateClaimExport(invalidClaim, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('validateEntityExport', () => {
  const validEntity = {
    id: 'ent_test',
    type: 'Concept',
    name: 'テストエンティティ',
  };

  it('有効なEntityはRight', () => {
    const result = validateEntityExport(validEntity, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('canonical_keyを含む有効なEntityはRight', () => {
    const entityWithKey = { ...validEntity, canonical_key: 'test_key' };
    const result = validateEntityExport(entityWithKey, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('attrsを含む有効なEntityはRight', () => {
    const entityWithAttrs = { ...validEntity, attrs: { key: 'value' } };
    const result = validateEntityExport(entityWithAttrs, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('typeが無効な場合はLeft', () => {
    const invalidEntity = { ...validEntity, type: 'InvalidType' };
    const result = validateEntityExport(invalidEntity, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });

  it('idが空の場合はLeft', () => {
    const invalidEntity = { ...validEntity, id: '' };
    const result = validateEntityExport(invalidEntity, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('validateRelationExport', () => {
  const validRelation = {
    id: 'rel_test',
    src_id: 'ent_a',
    dst_id: 'ent_b',
    type: 'KNOWS',
  };

  it('有効なRelationはRight', () => {
    const result = validateRelationExport(validRelation, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('propsを含む有効なRelationはRight', () => {
    const relationWithProps = { ...validRelation, props: { weight: 1.0 } };
    const result = validateRelationExport(relationWithProps, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('evidence_claim_idを含む有効なRelationはRight', () => {
    const relationWithEvidence = { ...validRelation, evidence_claim_id: 'clm_test' };
    const result = validateRelationExport(relationWithEvidence, 'test.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('src_idが空の場合はLeft', () => {
    const invalidRelation = { ...validRelation, src_id: '' };
    const result = validateRelationExport(invalidRelation, 'test.json');
    expect(E.isLeft(result)).toBe(true);
  });
});

describe('validateManifest', () => {
  const validManifest = {
    version: '1.0',
    pce_memory_version: '0.7.0',
    last_push_at: '2025-12-12T10:00:00Z',
  };

  it('有効なManifestはRight', () => {
    const result = validateManifest(validManifest, 'manifest.json');
    expect(E.isRight(result)).toBe(true);
  });

  it('versionが1.0でない場合はLeft', () => {
    const invalidManifest = { ...validManifest, version: '2.0' };
    const result = validateManifest(invalidManifest, 'manifest.json');
    expect(E.isLeft(result)).toBe(true);
  });
});

/**
 * Property-Based Tests for Conflict Detection (Issue #18 Phase 3)
 *
 * 衝突検出のCRDT特性を自動検証する
 */
import { describe, it, expect } from 'vitest';
import * as fc from 'fast-check';
import {
  detectClaimConflict,
  detectEntityConflict,
  detectRelationConflict,
  createEmptyConflictReport,
  addConflict,
  type Conflict,
} from '../src/sync/conflict.js';
import { BOUNDARY_STRICTNESS, mergeBoundaryClass } from '../src/sync/merge.js';
import type { BoundaryClass, EntityExport, RelationExport } from '../src/sync/schemas.js';

// Arbitraries
const boundaryClassArb = fc.constantFrom<BoundaryClass>('public', 'internal', 'pii', 'secret');
const entityTypeArb = fc.constantFrom('Actor', 'Artifact', 'Event', 'Concept') as fc.Arbitrary<
  'Actor' | 'Artifact' | 'Event' | 'Concept'
>;
const nonEmptyStringArb = fc.string({ minLength: 1, maxLength: 100 });
// fast-checkのhexaString APIが存在しないため、string()でhex文字列を生成
const hexChars = '0123456789abcdef';
const contentHashArb = fc
  .array(fc.constantFrom(...hexChars.split('')), { minLength: 64, maxLength: 64 })
  .map((chars) => `sha256:${chars.join('')}` as const);

describe('Property: CRDT Merge Laws', () => {
  it('Property: 冪等性 - mergeBoundaryClass(a, a) === a', () => {
    fc.assert(
      fc.property(boundaryClassArb, (bc) => {
        return mergeBoundaryClass(bc, bc) === bc;
      })
    );
  });

  it('Property: 可換性 - mergeBoundaryClass(a, b) === mergeBoundaryClass(b, a)', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        return mergeBoundaryClass(a, b) === mergeBoundaryClass(b, a);
      })
    );
  });

  it('Property: 結合律 - (a merge b) merge c === a merge (b merge c)', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, boundaryClassArb, (a, b, c) => {
        const leftAssoc = mergeBoundaryClass(mergeBoundaryClass(a, b), c);
        const rightAssoc = mergeBoundaryClass(a, mergeBoundaryClass(b, c));
        return leftAssoc === rightAssoc;
      })
    );
  });

  it('Property: 単調性 - マージ結果は両方より厳格度が高い', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        const merged = mergeBoundaryClass(a, b);
        return (
          BOUNDARY_STRICTNESS[merged] >= BOUNDARY_STRICTNESS[a] &&
          BOUNDARY_STRICTNESS[merged] >= BOUNDARY_STRICTNESS[b]
        );
      })
    );
  });

  it('Property: CRDT収束性 - 任意の順序でマージしても同じ結果', () => {
    fc.assert(
      fc.property(fc.array(boundaryClassArb, { minLength: 1, maxLength: 10 }), (classes) => {
        const leftFold = classes.reduce((acc, bc) => mergeBoundaryClass(acc, bc));
        const rightFold = [...classes].reverse().reduce((acc, bc) => mergeBoundaryClass(acc, bc));
        // シャッフルしてマージ
        const shuffled = [...classes].sort(() => Math.random() - 0.5);
        const shuffledFold = shuffled.reduce((acc, bc) => mergeBoundaryClass(acc, bc));
        return leftFold === rightFold && rightFold === shuffledFold;
      })
    );
  });
});

describe('Property: Claim Conflict Detection', () => {
  it('Property: 境界格上げ時のみconflictが発生', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, contentHashArb, (existing, incoming, hash) => {
        const conflict = detectClaimConflict({ boundary_class: existing }, {
          text: 'test',
          kind: 'fact',
          scope: 'project',
          boundary_class: incoming,
          content_hash: hash,
        });

        const isUpgrade = BOUNDARY_STRICTNESS[incoming] > BOUNDARY_STRICTNESS[existing];

        if (isUpgrade) {
          // 格上げの場合は boundary_upgrade conflict
          return conflict !== null && conflict.type === 'boundary_upgrade';
        } else {
          // 同一または格下げの場合は conflict なし
          return conflict === null;
        }
      })
    );
  });

  it('Property: 新規Claim（既存なし）はconflictなし', () => {
    fc.assert(
      fc.property(boundaryClassArb, contentHashArb, (incoming, hash) => {
        const conflict = detectClaimConflict(undefined, {
          text: 'test',
          kind: 'fact',
          scope: 'project',
          boundary_class: incoming,
          content_hash: hash,
        });
        return conflict === null;
      })
    );
  });

  it('Property: conflict検出は決定的（同じ入力に対して同じ結果）', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, contentHashArb, (existing, incoming, hash) => {
        const claim = {
          text: 'test',
          kind: 'fact' as const,
          scope: 'project' as const,
          boundary_class: incoming,
          content_hash: hash,
        };
        const conflict1 = detectClaimConflict({ boundary_class: existing }, claim);
        const conflict2 = detectClaimConflict({ boundary_class: existing }, claim);

        return JSON.stringify(conflict1) === JSON.stringify(conflict2);
      })
    );
  });
});

describe('Property: Entity Conflict Detection', () => {
  it('Property: 同一ID・同一内容はconflictなし', () => {
    fc.assert(
      fc.property(nonEmptyStringArb, entityTypeArb, nonEmptyStringArb, (id, type, name) => {
        const entity: EntityExport = { id, type, name };
        const conflict = detectEntityConflict(entity, entity);
        return conflict === null;
      })
    );
  });

  it('Property: 同一ID・異なる内容はconflictあり', () => {
    fc.assert(
      fc.property(
        nonEmptyStringArb,
        entityTypeArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        (id, type, name1, name2) => {
          fc.pre(name1 !== name2); // 異なる名前を前提

          const existing: EntityExport = { id, type, name: name1 };
          const incoming: EntityExport = { id, type, name: name2 };
          const conflict = detectEntityConflict(existing, incoming);

          return conflict !== null && conflict.type === 'entity_content_diff';
        }
      )
    );
  });

  it('Property: 新規Entity（既存なし）はconflictなし', () => {
    fc.assert(
      fc.property(nonEmptyStringArb, entityTypeArb, nonEmptyStringArb, (id, type, name) => {
        const conflict = detectEntityConflict(undefined, { id, type, name });
        return conflict === null;
      })
    );
  });
});

describe('Property: Relation Conflict Detection', () => {
  it('Property: 同一ID・同一内容はconflictなし', () => {
    fc.assert(
      fc.property(
        nonEmptyStringArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        (id, srcId, dstId, relType) => {
          const relation: RelationExport = { id, src_id: srcId, dst_id: dstId, type: relType };
          const conflict = detectRelationConflict(relation, relation);
          return conflict === null;
        }
      )
    );
  });

  it('Property: 同一ID・異なる内容はconflictあり', () => {
    fc.assert(
      fc.property(
        nonEmptyStringArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        nonEmptyStringArb,
        (id, srcId1, dstId, relType, srcId2) => {
          fc.pre(srcId1 !== srcId2); // 異なるsrc_idを前提

          const existing: RelationExport = { id, src_id: srcId1, dst_id: dstId, type: relType };
          const incoming: RelationExport = { id, src_id: srcId2, dst_id: dstId, type: relType };
          const conflict = detectRelationConflict(existing, incoming);

          return conflict !== null && conflict.type === 'relation_content_diff';
        }
      )
    );
  });
});

describe('Property: ConflictReport', () => {
  it('Property: 空レポートのカウントはすべて0', () => {
    const report = createEmptyConflictReport();
    expect(report.conflicts).toHaveLength(0);
    expect(report.autoResolved).toBe(0);
    expect(report.skipped).toBe(0);
  });

  it('Property: addConflictでカウントが正しく増加', () => {
    fc.assert(
      fc.property(
        fc.array(
          fc.record({
            type: fc.constantFrom(
              'boundary_upgrade',
              'entity_content_diff',
              'relation_content_diff',
              'missing_reference'
            ),
            resolution: fc.constantFrom('auto_resolved', 'skipped'),
          }),
          { minLength: 0, maxLength: 20 }
        ),
        (conflictData) => {
          let report = createEmptyConflictReport();

          for (const data of conflictData) {
            const conflict: Conflict = {
              type: data.type as Conflict['type'],
              id: 'test-id',
              resolution: data.resolution as Conflict['resolution'],
              message: 'test message',
            };
            report = addConflict(report, conflict);
          }

          const expectedAutoResolved = conflictData.filter(
            (d) => d.resolution === 'auto_resolved'
          ).length;
          const expectedSkipped = conflictData.filter((d) => d.resolution === 'skipped').length;

          return (
            report.conflicts.length === conflictData.length &&
            report.autoResolved === expectedAutoResolved &&
            report.skipped === expectedSkipped
          );
        }
      )
    );
  });
});

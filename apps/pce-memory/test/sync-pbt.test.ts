/**
 * Property-Based Tests for Sync (Issue #18)
 *
 * 法則の検証:
 * 1. Idempotency: 同じデータのpush/pullは同じ結果
 * 2. Boundary Never Downgrades: boundary_classは厳格な方向にのみ変化
 * 3. Content Hash Integrity: content_hashはテキストと常に一致
 */
import { describe, it } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash } from '@pce/embeddings';
import {
  mergeBoundaryClass,
  isBoundarySyncable,
  isBoundaryUpgraded,
  BOUNDARY_STRICTNESS,
} from '../src/sync/merge.js';
import { validateContentHashMatch } from '../src/sync/validation.js';
import * as E from 'fp-ts/Either';
import type { BoundaryClass } from '../src/sync/schemas.js';

// Arbitraries
const boundaryClassArb = fc.constantFrom<BoundaryClass>('public', 'internal', 'pii', 'secret');

const boundaryClassArrayArb = fc.array(boundaryClassArb, { minLength: 1, maxLength: 4 });

const nonEmptyTextArb = fc.string({ minLength: 1, maxLength: 1000 });

describe('Property: mergeBoundaryClass', () => {
  it('Property: マージ結果は常に入力の一方と等しい', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        const result = mergeBoundaryClass(a, b);
        return result === a || result === b;
      })
    );
  });

  it('Property: マージ結果は常に両方の入力以上の厳格さ', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        const result = mergeBoundaryClass(a, b);
        return (
          BOUNDARY_STRICTNESS[result] >= BOUNDARY_STRICTNESS[a] &&
          BOUNDARY_STRICTNESS[result] >= BOUNDARY_STRICTNESS[b]
        );
      })
    );
  });

  it('Property: マージは結合律を満たす', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, boundaryClassArb, (a, b, c) => {
        // (a merge b) merge c === a merge (b merge c)
        const left = mergeBoundaryClass(mergeBoundaryClass(a, b), c);
        const right = mergeBoundaryClass(a, mergeBoundaryClass(b, c));
        return left === right;
      })
    );
  });

  it('Property: マージは可換律を満たす', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        return mergeBoundaryClass(a, b) === mergeBoundaryClass(b, a);
      })
    );
  });

  it('Property: マージは冪等律を満たす', () => {
    fc.assert(
      fc.property(boundaryClassArb, (a) => {
        return mergeBoundaryClass(a, a) === a;
      })
    );
  });

  it('Property: secretとのマージは常にsecret', () => {
    fc.assert(
      fc.property(boundaryClassArb, (a) => {
        return mergeBoundaryClass(a, 'secret') === 'secret';
      })
    );
  });

  it('Property: publicとのマージは元の値を保持', () => {
    fc.assert(
      fc.property(boundaryClassArb, (a) => {
        return mergeBoundaryClass(a, 'public') === a;
      })
    );
  });
});

describe('Property: isBoundarySyncable', () => {
  it('Property: secretは常に同期不可', () => {
    fc.assert(
      fc.property(boundaryClassArrayArb, (allowed) => {
        return isBoundarySyncable('secret', allowed) === false;
      })
    );
  });

  it('Property: allowedに含まれるnon-secretは同期可能', () => {
    fc.assert(
      fc.property(fc.constantFrom<BoundaryClass>('public', 'internal', 'pii'), (bc) => {
        return isBoundarySyncable(bc, [bc]) === true;
      })
    );
  });
});

describe('Property: isBoundaryUpgraded', () => {
  it('Property: 同じ値は格上げではない', () => {
    fc.assert(
      fc.property(boundaryClassArb, (a) => {
        return isBoundaryUpgraded(a, a) === false;
      })
    );
  });

  it('Property: 厳格度が上がった場合のみtrue', () => {
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (before, after) => {
        const upgraded = isBoundaryUpgraded(before, after);
        if (upgraded) {
          return BOUNDARY_STRICTNESS[after] > BOUNDARY_STRICTNESS[before];
        }
        return BOUNDARY_STRICTNESS[after] <= BOUNDARY_STRICTNESS[before];
      })
    );
  });
});

describe('Property: content_hash', () => {
  it('Property: 同じテキストは常に同じハッシュ', () => {
    fc.assert(
      fc.property(nonEmptyTextArb, (text) => {
        const hash1 = computeContentHash(text);
        const hash2 = computeContentHash(text);
        return hash1 === hash2;
      })
    );
  });

  it('Property: 異なるテキストは（高確率で）異なるハッシュ', () => {
    fc.assert(
      fc.property(nonEmptyTextArb, nonEmptyTextArb, (text1, text2) => {
        // 同じテキストの場合はスキップ
        if (text1 === text2) return true;
        const hash1 = computeContentHash(text1);
        const hash2 = computeContentHash(text2);
        return hash1 !== hash2;
      })
    );
  });

  it('Property: validateContentHashMatchは正しいハッシュでRight', () => {
    fc.assert(
      fc.property(nonEmptyTextArb, (text) => {
        const hash = `sha256:${computeContentHash(text)}`;
        const result = validateContentHashMatch(text, hash, 'test.json');
        return E.isRight(result);
      })
    );
  });

  it('Property: validateContentHashMatchは不正なハッシュでLeft', () => {
    fc.assert(
      fc.property(nonEmptyTextArb, nonEmptyTextArb, (text1, text2) => {
        // 同じテキストの場合はスキップ
        if (text1 === text2) return true;
        const wrongHash = `sha256:${computeContentHash(text2)}`;
        const result = validateContentHashMatch(text1, wrongHash, 'test.json');
        return E.isLeft(result);
      })
    );
  });
});

describe('Property: Boundary Class CRDT Properties', () => {
  it('Property: マージはsemi-lattice join（最小上界）', () => {
    // join(a, b) >= a かつ join(a, b) >= b かつ
    // 任意のc >= a, c >= b について c >= join(a, b)
    fc.assert(
      fc.property(boundaryClassArb, boundaryClassArb, (a, b) => {
        const joined = mergeBoundaryClass(a, b);
        const joinedStrictness = BOUNDARY_STRICTNESS[joined];
        const aStrictness = BOUNDARY_STRICTNESS[a];
        const bStrictness = BOUNDARY_STRICTNESS[b];

        // joinは両方以上
        const isUpperBound = joinedStrictness >= aStrictness && joinedStrictness >= bStrictness;

        // joinは最小の上界（これは定義上常に真）
        const isLeastUpperBound = joinedStrictness === Math.max(aStrictness, bStrictness);

        return isUpperBound && isLeastUpperBound;
      })
    );
  });

  it('Property: 境界クラスマージはCRDT収束性を満たす', () => {
    // 任意の順序でマージしても最終結果は同じ
    fc.assert(
      fc.property(fc.array(boundaryClassArb, { minLength: 1, maxLength: 10 }), (classes) => {
        // 左から順にマージ
        const leftFold = classes.reduce((acc, bc) => mergeBoundaryClass(acc, bc));

        // 右から順にマージ
        const rightFold = [...classes].reverse().reduce((acc, bc) => mergeBoundaryClass(acc, bc));

        // シャッフルしてマージ
        const shuffled = [...classes].sort(() => Math.random() - 0.5);
        const shuffledFold = shuffled.reduce((acc, bc) => mergeBoundaryClass(acc, bc));

        return leftFold === rightFold && rightFold === shuffledFold;
      })
    );
  });
});

/**
 * Property-Based Tests for Sync (Issue #18)
 *
 * 法則の検証:
 * 1. Idempotency: 同じデータのpush/pullは同じ結果
 * 2. Boundary Never Downgrades: boundary_classは厳格な方向にのみ変化
 * 3. Content Hash Integrity: content_hashはテキストと常に一致
 */
import * as fs from 'node:fs/promises';
import * as os from 'node:os';
import * as path from 'node:path';
import { describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash } from '@pce/embeddings';
import {
  mergeBoundaryClass,
  isBoundarySyncable,
  isBoundaryUpgraded,
  BOUNDARY_STRICTNESS,
} from '../src/sync/merge.js';
import { validateContentHashMatch } from '../src/sync/validation.js';
import { executePull } from '../src/sync/pull.js';
import { executePush } from '../src/sync/push.js';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { findClaimByContentHash, upsertClaim } from '../src/store/claims.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import * as E from 'fp-ts/Either';
import type { BoundaryClass, ClaimExport, MemoryType, Scope } from '../src/sync/schemas.js';

// Arbitraries
const boundaryClassArb = fc.constantFrom<BoundaryClass>('public', 'internal', 'pii', 'secret');

const boundaryClassArrayArb = fc.array(boundaryClassArb, { minLength: 1, maxLength: 4 });

const nonEmptyTextArb = fc.string({ minLength: 1, maxLength: 1000 });
const syncableBoundaryClassArb = fc.constantFrom<BoundaryClass>('public', 'internal');
const durableScopeArb = fc.constantFrom<Scope>('project', 'principle');
const durableMemoryTypeArb = fc.constantFrom<MemoryType>(
  'working_state',
  'knowledge',
  'procedure',
  'norm'
);
const durableKindArb = fc.constantFrom<'fact' | 'preference' | 'task' | 'policy_hint'>(
  'fact',
  'preference',
  'task',
  'policy_hint'
);
const durableClaimArb = fc.record({
  text: fc.string({ minLength: 1, maxLength: 80 }),
  kind: durableKindArb,
  scope: durableScopeArb,
  boundary_class: syncableBoundaryClassArb,
  memory_type: durableMemoryTypeArb,
});
const mixedClaimArb = fc.record({
  text: fc.string({ minLength: 1, maxLength: 80 }),
  kind: durableKindArb,
  scope: fc.constantFrom<Scope>('session', 'project', 'principle'),
  boundary_class: syncableBoundaryClassArb,
  tombstoned: fc.boolean(),
});

async function initSyncTestDb(): Promise<void> {
  await resetDbAsync();
  resetMemoryState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

async function withTempDir<T>(run: (tempDir: string) => Promise<T>): Promise<T> {
  const tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-pbt-'));
  try {
    return await run(tempDir);
  } finally {
    await fs.rm(tempDir, { recursive: true, force: true });
  }
}

async function markClaimTombstoned(contentHash: string): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    `UPDATE claims
     SET tombstone = TRUE,
         tombstone_at = $1::TIMESTAMP,
         rollback_reason = $2
     WHERE content_hash = $3`,
    ['2026-03-24T00:00:00.000Z', 'property-based tombstone', contentHash]
  );
}

async function readExportedClaims(basePath: string): Promise<ClaimExport[]> {
  const exports: ClaimExport[] = [];
  const syncRoot = path.join(basePath, '.pce-shared', 'claims');

  for (const scope of ['session', 'project', 'principle'] as const) {
    const scopeDir = path.join(syncRoot, scope);
    let files: string[] = [];
    try {
      files = await fs.readdir(scopeDir);
    } catch {
      continue;
    }

    for (const file of files) {
      if (!file.endsWith('.json')) {
        continue;
      }
      const content = await fs.readFile(path.join(scopeDir, file), 'utf-8');
      exports.push(JSON.parse(content) as ClaimExport);
    }
  }

  return exports;
}

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

describe('Property: Sync Integration Invariants', () => {
  it('Property: memory_type is preserved across push/pull round-trip', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uniqueArray(durableClaimArb, {
          selector: (claim) => claim.text,
          maxLength: 4,
        }),
        async (claims) => {
          return withTempDir(async (tempDir) => {
            await initSyncTestDb();

            for (const claim of claims) {
              await upsertClaim({
                ...claim,
                content_hash: `sha256:${computeContentHash(claim.text)}`,
              });
            }

            const pushResult = await executePush({
              basePath: tempDir,
              boundaryFilter: ['public', 'internal', 'pii'],
            });
            expect(E.isRight(pushResult)).toBe(true);

            await initSyncTestDb();

            const pullResult = await executePull({
              basePath: tempDir,
              boundaryFilter: ['public', 'internal', 'pii'],
            });
            expect(E.isRight(pullResult)).toBe(true);

            for (const claim of claims) {
              const saved = await findClaimByContentHash(
                `sha256:${computeContentHash(claim.text)}`
              );
              expect(saved?.memory_type).toBe(claim.memory_type);
            }
          });
        }
      ),
      { numRuns: 12 }
    );
  });

  it('Property: session claims never appear in export', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uniqueArray(mixedClaimArb, {
          selector: (claim) => claim.text,
          maxLength: 5,
        }),
        async (claims) => {
          return withTempDir(async (tempDir) => {
            await initSyncTestDb();

            for (const claim of claims) {
              const contentHash = `sha256:${computeContentHash(claim.text)}`;
              await upsertClaim({
                text: claim.text,
                kind: claim.kind,
                scope: claim.scope,
                boundary_class: claim.boundary_class,
                content_hash: contentHash,
              });

              if (claim.tombstoned) {
                await markClaimTombstoned(contentHash);
              }
            }

            const pushResult = await executePush({
              basePath: tempDir,
              scopeFilter: ['session', 'project', 'principle'],
              boundaryFilter: ['public', 'internal', 'pii'],
            });
            expect(E.isRight(pushResult)).toBe(true);

            const exportedClaims = await readExportedClaims(tempDir);
            expect(exportedClaims.every((claim) => claim.scope !== 'session')).toBe(true);
          });
        }
      ),
      { numRuns: 12 }
    );
  });

  it('Property: tombstoned claims never appear in export', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.uniqueArray(mixedClaimArb, {
          selector: (claim) => claim.text,
          maxLength: 5,
        }),
        async (claims) => {
          return withTempDir(async (tempDir) => {
            await initSyncTestDb();

            const tombstonedHashes = new Set<string>();

            for (const claim of claims) {
              const contentHash = `sha256:${computeContentHash(claim.text)}`;
              await upsertClaim({
                text: claim.text,
                kind: claim.kind,
                scope: claim.scope,
                boundary_class: claim.boundary_class,
                content_hash: contentHash,
              });

              if (claim.tombstoned) {
                tombstonedHashes.add(contentHash);
                await markClaimTombstoned(contentHash);
              }
            }

            const pushResult = await executePush({
              basePath: tempDir,
              scopeFilter: ['session', 'project', 'principle'],
              boundaryFilter: ['public', 'internal', 'pii'],
            });
            expect(E.isRight(pushResult)).toBe(true);

            const exportedClaims = await readExportedClaims(tempDir);
            const exportedHashes = new Set(exportedClaims.map((claim) => claim.content_hash));
            expect([...tombstonedHashes].every((hash) => !exportedHashes.has(hash))).toBe(true);
          });
        }
      ),
      { numRuns: 12 }
    );
  });
});

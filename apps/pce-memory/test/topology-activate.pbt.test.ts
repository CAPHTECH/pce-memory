import { beforeEach, describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { computeContentHash, type EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { dispatchTool } from '../src/core/handlers';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetMemoryState } from '../src/state/memoryState';
import { initRateState, resetRates } from '../src/store/rate';
import { setEmbeddingService } from '../src/store/hybridSearch';

function normalize(vector: readonly number[]): readonly number[] {
  const magnitude = Math.sqrt(vector.reduce((sum, value) => sum + value * value, 0));
  if (magnitude === 0) {
    return [1, 0];
  }
  return vector.map((value) => Number((value / magnitude).toFixed(6)));
}

function createEmbeddingService(embeddings: Record<string, readonly number[]>): EmbeddingService {
  return {
    embed:
      ({ text }) =>
      async () =>
        E.right({
          embedding: embeddings[text] ?? normalize([-1, 0]),
          modelVersion: 'topology-pbt-v1',
        }),
  };
}

async function applyPolicy(): Promise<void> {
  await dispatchTool('pce_memory_policy_apply', {});
}

async function resetTopologyHarness(): Promise<void> {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
}

async function upsertKnowledge(text: string): Promise<string> {
  const result = await dispatchTool('pce_memory_upsert', {
    text,
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    memory_type: 'knowledge',
    content_hash: `sha256:${computeContentHash(text)}`,
    provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'vitest' },
  });
  return result.structuredContent!.id as string;
}

beforeEach(async () => {
  await resetTopologyHarness();
});

describe('Property: topology-aware activate invariants', () => {
  it('Property: related traversal never exceeds two hops', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.integer({ min: 3, max: 5 }),
        fc.stringMatching(/^[a-z0-9]{1,12}$/),
        async (chainLength, token) => {
          await resetTopologyHarness();
          const texts = Array.from(
            { length: chainLength },
            (_, index) => `chain-${token}-${index}`
          );
          const queryText = `query-${token}`;
          setEmbeddingService(
            createEmbeddingService({
              [texts[0]!]: normalize([1, 0]),
              [queryText]: normalize([1, 0]),
            })
          );
          await applyPolicy();

          const ids: string[] = [];
          for (const text of texts) {
            ids.push(await upsertKnowledge(text));
          }
          for (let index = 0; index < ids.length - 1; index++) {
            await dispatchTool('pce_memory_link_claims', {
              source_claim_id: ids[index]!,
              target_claim_id: ids[index + 1]!,
              link_type: 'related',
            });
          }

          const activate = (await dispatchTool('pce_memory_activate', {
            scope: ['project'],
            allow: ['answer:task'],
            q: queryText,
            top_k: chainLength,
          }).then((result) => result.structuredContent)) as {
            claims: Array<{
              claim: { id: string };
              topology?: { path?: unknown[] };
            }>;
          };

          const returnedIds = activate.claims.map((item) => item.claim.id);
          expect(returnedIds).toContain(ids[0]);
          expect(returnedIds).toContain(ids[1]);
          expect(returnedIds).toContain(ids[2]);
          for (let index = 3; index < ids.length; index++) {
            expect(returnedIds).not.toContain(ids[index]);
          }
          for (const item of activate.claims) {
            expect(item.topology?.path?.length ?? 0).toBeLessThanOrEqual(2);
          }
        }
      ),
      { numRuns: 16 }
    );
  });

  it('Property: contradiction edges do not propagate to downstream neighbors', async () => {
    await fc.assert(
      fc.asyncProperty(fc.stringMatching(/^[a-z0-9]{1,12}$/), async (token) => {
        await resetTopologyHarness();
        const anchorText = `anchor-${token}`;
        const conflictText = `conflict-${token}`;
        const downstreamText = `downstream-${token}`;
        const queryText = `query-${token}`;
        setEmbeddingService(
          createEmbeddingService({
            [anchorText]: normalize([1, 0]),
            [queryText]: normalize([1, 0]),
          })
        );
        await applyPolicy();

        const anchorId = await upsertKnowledge(anchorText);
        const conflictId = await upsertKnowledge(conflictText);
        const downstreamId = await upsertKnowledge(downstreamText);

        await dispatchTool('pce_memory_link_claims', {
          source_claim_id: conflictId,
          target_claim_id: anchorId,
          link_type: 'contradicts',
        });
        await dispatchTool('pce_memory_link_claims', {
          source_claim_id: conflictId,
          target_claim_id: downstreamId,
          link_type: 'related',
        });

        const activate = (await dispatchTool('pce_memory_activate', {
          scope: ['project'],
          allow: ['answer:task'],
          q: queryText,
          top_k: 5,
        }).then((result) => result.structuredContent)) as {
          claims: Array<{ claim: { id: string } }>;
        };

        const returnedIds = activate.claims.map((item) => item.claim.id);
        expect(returnedIds).toContain(anchorId);
        expect(returnedIds).toContain(conflictId);
        expect(returnedIds).not.toContain(downstreamId);
      }),
      { numRuns: 16 }
    );
  });
});

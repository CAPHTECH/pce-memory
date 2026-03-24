import { describe, expect, it } from 'vitest';
import * as fc from 'fast-check';
import { dispatchTool } from '../src/core/handlers';
import { findActiveContextById } from '../src/store/activeContext';
import type { ClaimKind, MemoryType } from '../src/domain/types';
import { getConnection } from '../src/db/connection';
import {
  applyPolicy,
  insertClaimDirect,
  resetRetrievalPlannerTestState,
} from './helpers/retrievalPlannerTestUtils';

const boundaryClassArb = fc.constantFrom<'public' | 'internal' | 'pii' | 'secret'>(
  'public',
  'internal',
  'pii',
  'secret'
);
const claimKindArb = fc.constantFrom<ClaimKind>('fact', 'preference', 'task', 'policy_hint');
const memoryTypeArb = fc.option(
  fc.constantFrom<MemoryType>('evidence', 'working_state', 'knowledge', 'procedure', 'norm'),
  { nil: undefined }
);
const allowTagArb = fc.constantFrom('answer:task', 'answer:other', 'tool:contact-lookup');
const intentArb = fc.option(
  fc.constantFrom('resume_task', 'debug_incident', 'design_decision', 'policy_check'),
  { nil: undefined }
);

function allowedBoundaryClassesFor(allowTag: string): string[] {
  const allowed = new Set<string>(['public']);
  if (allowTag === 'answer:task' || allowTag.startsWith('tool:')) {
    allowed.add('internal');
  }
  if (allowTag === 'tool:contact-lookup') {
    allowed.add('pii');
  }
  return [...allowed];
}

async function countActiveContextItems(activeContextId: string): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT COUNT(*)::INTEGER AS cnt FROM active_context_items WHERE active_context_id = $1',
    [activeContextId]
  );
  const rows = reader.getRowObjects() as Array<{ cnt: number }>;
  return rows[0]?.cnt ?? 0;
}

describe('Property: retrieval planner invariants', () => {
  it('Property: scores stay non-negative, counts stay within top_k, active_context_items align, breakdowns compose, and boundary filters never leak', async () => {
    await fc.assert(
      fc.asyncProperty(
        fc.array(
          fc.record({
            boundary_class: boundaryClassArb,
            kind: claimKindArb,
            memory_type: memoryTypeArb,
          }),
          { minLength: 0, maxLength: 8 }
        ),
        allowTagArb,
        fc.integer({ min: 1, max: 6 }),
        intentArb,
        async (claims, allowTag, topK, intent) => {
          await resetRetrievalPlannerTestState();
          await applyPolicy({ threshold: 0.0 });

          for (let index = 0; index < claims.length; index++) {
            const claim = claims[index]!;
            await insertClaimDirect({
              text: `property retrieval ${index} ${claim.boundary_class} ${claim.kind}`,
              kind: claim.kind,
              scope: 'project',
              boundary_class: claim.boundary_class,
              ...(claim.memory_type ? { memory_type: claim.memory_type } : {}),
              content_hash: `sha256:property-retrieval-${index}-${claim.boundary_class}-${claim.kind}`,
            });
          }

          const activate = await dispatchTool('pce_memory_activate', {
            scope: ['project'],
            allow: [allowTag],
            top_k: topK,
            ...(intent ? { intent } : {}),
          });

          expect(activate.isError).toBeUndefined();
          const body = activate.structuredContent as {
            active_context_id: string;
            claims_count: number;
            claims: Array<{
              score: number;
              claim: { boundary_class: string };
              score_breakdown?: {
                S: number;
                g: { g: number };
                score_final: number;
                intent?: { boost?: number };
              };
            }>;
          };

          const allowedBoundaryClasses = allowedBoundaryClassesFor(allowTag);

          expect(body.claims_count).toBeLessThanOrEqual(topK);
          expect(body.claims).toHaveLength(body.claims_count);
          expect(await countActiveContextItems(body.active_context_id)).toBe(body.claims.length);

          const activeContext = await findActiveContextById(body.active_context_id);
          expect(activeContext?.claims).toHaveLength(body.claims.length);

          for (const item of body.claims) {
            expect(item.score).toBeGreaterThanOrEqual(0);
            expect(allowedBoundaryClasses).toContain(item.claim.boundary_class);

            const breakdown = item.score_breakdown;
            expect(breakdown).toBeDefined();
            const boost = breakdown?.intent?.boost ?? 1;
            expect(item.score).toBeCloseTo(breakdown?.score_final ?? Number.NaN, 10);
            expect(breakdown?.score_final ?? Number.NaN).toBeGreaterThanOrEqual(0);
            expect(breakdown?.score_final ?? Number.NaN).toBeCloseTo(
              (breakdown?.S ?? Number.NaN) * (breakdown?.g.g ?? Number.NaN) * boost,
              10
            );
          }
        }
      ),
      { numRuns: 24 }
    );
  });
});

import { beforeEach, describe, expect, it } from 'vitest';
import { dispatchTool } from '../src/core/handlers';
import { getConnection } from '../src/db/connection';
import { findActiveContextById } from '../src/store/activeContext';
import { insertPromotionQueueRow } from '../src/store/promotionQueue';
import { saveClaimVector, setEmbeddingService } from '../src/store/hybridSearch';
import { updateCritic } from '../src/store/critic';
import {
  applyPolicy,
  createMockEmbeddingService,
  insertClaimDirect,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).not.toBe(true);
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
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

describe('systematic retrieval planner boundary coverage', () => {
  it('allows activate with 0 claims after policy apply', async () => {
    await applyPolicy();

    const activate = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 5,
    });

    const body = expectSuccess(activate) as {
      active_context_id: string;
      claims: unknown[];
      claims_count: number;
    };
    expect(body.claims_count).toBe(0);
    expect(body.claims).toEqual([]);
    expect(await countActiveContextItems(body.active_context_id)).toBe(0);

    const activeContext = await findActiveContextById(body.active_context_id);
    expect(activeContext?.claims).toEqual([]);
  });

  it('persists a single active_context_item when exactly one claim matches', async () => {
    await applyPolicy();
    expectSuccess(
      await upsertClaimViaTool({
        text: 'single retrieval candidate',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'single retrieval',
        top_k: 5,
      })
    ) as {
      active_context_id: string;
      claims: Array<{ claim: { text: string } }>;
      claims_count: number;
    };

    expect(activate.claims_count).toBe(1);
    expect(activate.claims[0]?.claim.text).toContain('single retrieval candidate');
    expect(await countActiveContextItems(activate.active_context_id)).toBe(1);
  });

  it('respects top_k=1 and top_k=50 on queryless activation', async () => {
    await applyPolicy();

    for (let index = 0; index < 60; index++) {
      await insertClaimDirect({
        text: `queryless retrieval ${index}`,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: `sha256:top-k-${index}`,
      });
    }

    const firstPage = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        top_k: 1,
      })
    ) as {
      claims_count: number;
      has_more: boolean;
      next_cursor?: string;
    };
    expect(firstPage.claims_count).toBe(1);
    expect(firstPage.has_more).toBe(true);
    expect(firstPage.next_cursor).toBeDefined();

    const largePage = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        top_k: 50,
      })
    ) as {
      claims_count: number;
      has_more: boolean;
      next_cursor?: string;
    };
    expect(largePage.claims_count).toBe(50);
    expect(largePage.has_more).toBe(true);
    expect(largePage.next_cursor).toBeDefined();
  });

  it('treats an empty query as queryless retrieval', async () => {
    await applyPolicy();
    expectSuccess(await upsertClaimViaTool({ text: 'empty query first', kind: 'fact' }));
    expectSuccess(await upsertClaimViaTool({ text: 'empty query second', kind: 'task' }));

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: '',
        top_k: 10,
      })
    ) as {
      claims_count: number;
    };

    expect(activate.claims_count).toBe(2);
  });

  it('accepts very long queries without truncating matching results', async () => {
    await applyPolicy();
    expectSuccess(
      await upsertClaimViaTool({
        text: 'planner long query anchor',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    );
    const longQuery = `planner ${'x'.repeat(8_192)}`;

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: longQuery,
        top_k: 5,
      })
    ) as {
      claims_count: number;
      claims: Array<{ claim: { text: string } }>;
    };

    expect(activate.claims_count).toBe(1);
    expect(activate.claims[0]?.claim.text).toBe('planner long query anchor');
  });

  it('returns zero results when kind_filter removes all kinds', async () => {
    await applyPolicy();
    expectSuccess(await upsertClaimViaTool({ text: 'kind filter boundary', kind: 'fact' }));

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'kind filter',
        kind_filter: [],
        top_k: 10,
      })
    ) as {
      claims_count: number;
    };

    expect(activate.claims_count).toBe(0);
  });

  it('returns zero results when memory_type_filter removes all memory types', async () => {
    await applyPolicy();
    expectSuccess(
      await upsertClaimViaTool({
        text: 'memory type filter boundary',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'memory type filter',
        memory_type_filter: [],
        top_k: 10,
      })
    ) as {
      claims_count: number;
    };

    expect(activate.claims_count).toBe(0);
  });
});

describe('systematic retrieval planner edge coverage', () => {
  it('changes ranking order when intent policy_check boosts policy hints', async () => {
    await applyPolicy({ threshold: 0.0 });

    const factId = expectSuccess(
      await upsertClaimViaTool({
        text: 'retention policy release note',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const policyId = expectSuccess(
      await upsertClaimViaTool({
        text: 'retention policy must be approved before release',
        kind: 'policy_hint',
        memory_type: 'norm',
      })
    ).id as string;

    await updateCritic(factId, 0.8, 0, 1);
    await updateCritic(policyId, 0.75, 0, 1);

    const base = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'retention policy release',
        top_k: 2,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };
    expect(base.claims[0]?.claim.id).toBe(factId);

    const intentAware = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'retention policy release',
        intent: 'policy_check',
        top_k: 2,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };
    expect(intentAware.claims[0]?.claim.id).toBe(policyId);
  });

  it('returns zero results when filtering to a valid kind absent from the candidate set', async () => {
    await applyPolicy();
    expectSuccess(await upsertClaimViaTool({ text: 'absent task kind', kind: 'fact' }));

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'absent task',
        kind_filter: ['task'],
        top_k: 10,
      })
    ) as {
      claims_count: number;
    };

    expect(activate.claims_count).toBe(0);
  });

  it('skips null memory_type claims when memory_type_filter is provided', async () => {
    await applyPolicy();
    expectSuccess(await upsertClaimViaTool({ text: 'legacy runbook note', kind: 'fact' }));
    expectSuccess(
      await upsertClaimViaTool({
        text: 'legacy runbook procedure',
        kind: 'fact',
        memory_type: 'procedure',
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'legacy runbook',
        memory_type_filter: ['procedure'],
        top_k: 10,
      })
    ) as {
      claims_count: number;
      claims: Array<{ claim: { memory_type?: string | null } }>;
    };

    expect(activate.claims_count).toBe(1);
    expect(activate.claims[0]?.claim.memory_type).toBe('procedure');
  });

  it('paginates across filtered sets using the filtered cursor order', async () => {
    await applyPolicy();

    const taskOne = expectSuccess(
      await upsertClaimViaTool({
        text: 'pager task one',
        kind: 'task',
        memory_type: 'working_state',
      })
    ).id as string;
    const taskTwo = expectSuccess(
      await upsertClaimViaTool({
        text: 'pager task two',
        kind: 'task',
        memory_type: 'working_state',
      })
    ).id as string;
    const taskThree = expectSuccess(
      await upsertClaimViaTool({
        text: 'pager task three',
        kind: 'task',
        memory_type: 'working_state',
      })
    ).id as string;
    const filteredOutFact = expectSuccess(
      await upsertClaimViaTool({
        text: 'pager fact noise',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const filteredOutPii = await insertClaimDirect({
      text: 'pager pii task',
      kind: 'task',
      scope: 'project',
      boundary_class: 'pii',
      memory_type: 'working_state',
      content_hash: 'sha256:pager-pii',
    });

    await updateCritic(taskOne, 0.9, 0, 1);
    await updateCritic(taskTwo, 0.8, 0, 1);
    await updateCritic(taskThree, 0.7, 0, 1);
    await updateCritic(filteredOutFact, 0.95, 0, 1);
    await updateCritic(filteredOutPii.id, 0.99, 0, 1);

    const page1 = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'pager',
        kind_filter: ['task'],
        top_k: 1,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
      has_more: boolean;
      next_cursor?: string;
    };
    expect(page1.claims[0]?.claim.id).toBe(taskOne);
    expect(page1.has_more).toBe(true);

    const page2 = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'pager',
        kind_filter: ['task'],
        top_k: 1,
        cursor: page1.next_cursor,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
      has_more: boolean;
      next_cursor?: string;
    };
    expect(page2.claims[0]?.claim.id).toBe(taskTwo);
    expect(page2.has_more).toBe(true);

    const page3 = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'pager',
        kind_filter: ['task'],
        top_k: 1,
        cursor: page2.next_cursor,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
      has_more: boolean;
    };
    expect(page3.claims[0]?.claim.id).toBe(taskThree);
    expect(page3.has_more).toBe(false);
  });

  it('supports concurrent activate calls and persists separate active contexts', async () => {
    await applyPolicy();
    expectSuccess(await upsertClaimViaTool({ text: 'concurrent activate first', kind: 'fact' }));
    expectSuccess(await upsertClaimViaTool({ text: 'concurrent activate second', kind: 'task' }));

    const [first, second] = await Promise.all([
      dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'concurrent activate',
        top_k: 1,
      }),
      dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'concurrent activate',
        top_k: 2,
        intent: 'resume_task',
      }),
    ]);

    const firstBody = expectSuccess(first) as {
      active_context_id: string;
      claims_count: number;
    };
    const secondBody = expectSuccess(second) as {
      active_context_id: string;
      claims_count: number;
    };

    expect(firstBody.active_context_id).not.toBe(secondBody.active_context_id);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT COUNT(*)::INTEGER AS cnt FROM active_contexts');
    const rows = reader.getRowObjects() as Array<{ cnt: number }>;
    expect(rows[0]?.cnt).toBe(2);
    expect(await countActiveContextItems(firstBody.active_context_id)).toBe(firstBody.claims_count);
    expect(await countActiveContextItems(secondBody.active_context_id)).toBe(secondBody.claims_count);
  });

  it('continues to activate after rollback while excluding rolled-back claims', async () => {
    await applyPolicy();

    const keepId = expectSuccess(
      await upsertClaimViaTool({
        text: 'rollback survivor claim',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const rolledBackId = expectSuccess(
      await upsertClaimViaTool({
        text: 'rollback removed claim',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;

    expectSuccess(
      await dispatchTool('pce_memory_rollback', {
        claim_id: rolledBackId,
        reason: 'superseded by a safer retrieval plan',
        provenance: { at: isoOffset(-60_000), actor: 'claude' },
      })
    );

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'rollback',
        top_k: 10,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toEqual([keepId]);
  });
});

describe('systematic retrieval planner failure modes', () => {
  it('rejects invalid intent values', async () => {
    await applyPolicy();

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      intent: 'ship_it',
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('intent must be one of');
  });

  it('supports alpha=0 as a pure lexical policy', async () => {
    await applyPolicy({ alpha: 0, threshold: 0.0 });
    setEmbeddingService(createMockEmbeddingService([1, 0]));

    const lexicalId = expectSuccess(
      await upsertClaimViaTool({
        text: 'alpha zero lexical keyword',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const semanticId = expectSuccess(
      await upsertClaimViaTool({
        text: 'semantic candidate without keyword',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;

    await saveClaimVector(lexicalId, [-1, 0], 'mock-v1');
    await saveClaimVector(semanticId, [1, 0], 'mock-v1');

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'alpha zero lexical',
        top_k: 2,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims[0]?.claim.id).toBe(lexicalId);
  });

  it('supports alpha=1 as a pure vector policy', async () => {
    await applyPolicy({ alpha: 1, threshold: 0.0 });
    setEmbeddingService(createMockEmbeddingService([1, 0]));

    const lexicalId = expectSuccess(
      await upsertClaimViaTool({
        text: 'alpha one lexical keyword',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const semanticId = expectSuccess(
      await upsertClaimViaTool({
        text: 'semantic candidate without keyword',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;

    await saveClaimVector(lexicalId, [-1, 0], 'mock-v1');
    await saveClaimVector(semanticId, [1, 0], 'mock-v1');

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'alpha one lexical',
        top_k: 2,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims[0]?.claim.id).toBe(semanticId);
  });

  it('keeps text matches when some candidate claims are missing embeddings', async () => {
    await applyPolicy();
    setEmbeddingService(createMockEmbeddingService([1, 0]));

    const textOnlyId = expectSuccess(
      await upsertClaimViaTool({
        text: 'missing embedding lexical match',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;
    const semanticId = expectSuccess(
      await upsertClaimViaTool({
        text: 'vector only semantic match',
        kind: 'fact',
        memory_type: 'knowledge',
      })
    ).id as string;

    await saveClaimVector(semanticId, [1, 0], 'mock-v1');

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:task'],
        q: 'missing embedding lexical',
        top_k: 5,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toContain(textOnlyId);
    expect(activate.claims.map((item) => item.claim.id)).toContain(semanticId);
  });

  it('keeps mixed boundary classes behind restrictive allow tags', async () => {
    await applyPolicy();

    const publicClaim = await insertClaimDirect({
      text: 'public retrieval note',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'public',
      content_hash: 'sha256:public-note',
    });
    await insertClaimDirect({
      text: 'internal retrieval note',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:internal-note',
    });
    await insertClaimDirect({
      text: 'pii retrieval note',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'pii',
      content_hash: 'sha256:pii-note',
    });
    const secretClaim = await insertClaimDirect({
      text: 'secret retrieval note',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'secret',
      content_hash: 'sha256:secret-note',
    });

    await insertPromotionQueueRow({
      id: 'rbk_secret_note',
      source_layer: 'meso',
      target_layer: 'meso',
      source_ids: JSON.stringify([secretClaim.id]),
      distilled_text: secretClaim.text,
      candidate_hash: 'sha256:rollback-secret-note',
      proposed_kind: secretClaim.kind,
      proposed_scope: secretClaim.scope,
      proposed_boundary_class: secretClaim.boundary_class,
      provenance: JSON.stringify({ rollback_of: secretClaim.id }),
      evidence_ids: JSON.stringify([]),
      boundary_check_result: JSON.stringify({ allowed: false }),
      status: 'rolled_back',
      created_at: '2026-03-24T12:00:00.000Z',
      resolved_at: '2026-03-24T12:00:00.000Z',
      accepted_claim_id: secretClaim.id,
      rejected_reason: 'test setup',
    });

    const activate = expectSuccess(
      await dispatchTool('pce_memory_activate', {
        scope: ['project'],
        allow: ['answer:other'],
        q: 'retrieval note',
        top_k: 10,
      })
    ) as {
      claims: Array<{ claim: { id: string } }>;
    };

    expect(activate.claims.map((item) => item.claim.id)).toEqual([publicClaim.id]);
  });
});

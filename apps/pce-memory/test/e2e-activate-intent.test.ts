import { beforeEach, describe, expect, it } from 'vitest';
import { dispatchTool } from '../src/core/handlers';
import { getConnection } from '../src/db/connection';
import { updateCritic } from '../src/store/critic';
import {
  applyPolicy,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

type ClaimKind = 'fact' | 'preference' | 'task' | 'policy_hint';
type MemoryType = 'evidence' | 'working_state' | 'knowledge' | 'procedure' | 'norm';
type ActivateIntent = 'resume_task' | 'policy_check' | 'design_decision' | 'debug_incident';

type ActivateClaim = {
  claim: {
    id: string;
    kind: ClaimKind;
    memory_type?: MemoryType | null;
    scope: 'session' | 'project' | 'principle';
  };
  source_layer?: string;
  score?: number;
  score_breakdown?: {
    score_final?: number;
    intent?: {
      boost?: number;
    };
  };
  selection_reason?: string;
  rank?: number;
};

type ActivateResponse = {
  active_context_id: string;
  intent?: ActivateIntent;
  claims: ActivateClaim[];
  claims_count: number;
  has_more: boolean;
  next_cursor?: string;
};

type ActiveContextItemRow = {
  claim_id: string;
  source_layer: string | null;
  rank: number | null;
  score_breakdown: string | null;
  selection_reason: string | null;
};

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
  await applyPolicy({ threshold: 0.0 });
});

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  if (result.isError === true) {
    throw new Error(JSON.stringify(result.structuredContent ?? result.content ?? result, null, 2));
  }
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

async function createClaim(input: {
  text: string;
  kind?: ClaimKind;
  memory_type?: MemoryType;
  scope?: 'session' | 'project' | 'principle';
  critic?: number;
  ageDays?: number;
}): Promise<string> {
  const upsert = expectSuccess(
    await upsertClaimViaTool({
      text: input.text,
      kind: input.kind,
      memory_type: input.memory_type,
      scope: input.scope,
    })
  ) as { id: string };

  if (input.critic !== undefined) {
    await updateCritic(upsert.id, input.critic, 0, 100);
  }

  if (input.ageDays !== undefined) {
    await setClaimAgeDays(upsert.id, input.ageDays);
  }

  return upsert.id;
}

async function setClaimAgeDays(claimId: string, ageDays: number): Promise<void> {
  const conn = await getConnection();
  const ts = new Date(Date.now() - ageDays * 24 * 60 * 60 * 1000).toISOString();
  await conn.run(
    'UPDATE claims SET created_at = $1, updated_at = $1, recency_anchor = $1 WHERE id = $2',
    [ts, claimId]
  );
}

async function createObservation(content: string): Promise<string> {
  const observation = expectSuccess(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      boundary_class: 'internal',
      extract: { mode: 'noop' },
    })
  ) as { observation_id: string };

  return observation.observation_id;
}

async function promoteObservations(
  contents: string[],
  note: string,
  critic?: number
): Promise<string> {
  const observationIds = await Promise.all(contents.map((content) => createObservation(content)));
  const distill = expectSuccess(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: observationIds,
      note,
    })
  ) as { candidate_id: string };

  const promote = expectSuccess(
    await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
      provenance: {
        at: new Date().toISOString(),
        actor: 'codex',
        note: `promoted for ${note}`,
      },
      reviewers: ['codex'],
      review_note: note,
    })
  ) as { claim_id: string };

  if (critic !== undefined) {
    await updateCritic(promote.claim_id, critic, 0, 100);
  }

  return promote.claim_id;
}

async function activate(args: {
  q?: string;
  top_k?: number;
  cursor?: string;
  scope?: Array<'session' | 'project' | 'principle'>;
  intent?: ActivateIntent;
  kind_filter?: ClaimKind[];
  memory_type_filter?: MemoryType[];
}): Promise<ActivateResponse> {
  return expectSuccess(
    await dispatchTool('pce_memory_activate', {
      scope: args.scope ?? ['project'],
      allow: ['answer:task'],
      ...(args.q !== undefined ? { q: args.q } : {}),
      ...(args.top_k !== undefined ? { top_k: args.top_k } : {}),
      ...(args.cursor !== undefined ? { cursor: args.cursor } : {}),
      ...(args.intent !== undefined ? { intent: args.intent } : {}),
      ...(args.kind_filter !== undefined ? { kind_filter: args.kind_filter } : {}),
      ...(args.memory_type_filter !== undefined
        ? { memory_type_filter: args.memory_type_filter }
        : {}),
    })
  ) as ActivateResponse;
}

async function getActiveContextItems(activeContextId: string): Promise<ActiveContextItemRow[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT claim_id, source_layer, rank, score_breakdown, selection_reason
     FROM active_context_items
     WHERE active_context_id = $1
     ORDER BY rank`,
    [activeContextId]
  );

  return reader.getRowObjects() as ActiveContextItemRow[];
}

function claimIds(response: ActivateResponse): string[] {
  return response.claims.map((item) => item.claim.id);
}

describe('E2E activate intent', () => {
  it('RESUME_TASK ranks task working_state above norm claims', async () => {
    const query = 'resume intent fixture';
    const taskId = await createClaim({
      text: `${query} task handoff in progress`,
      kind: 'task',
      memory_type: 'working_state',
      critic: 0.8,
    });
    const factId = await createClaim({
      text: `${query} architecture status`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.9,
    });
    const normId = await createClaim({
      text: `${query} approval must be documented`,
      kind: 'policy_hint',
      memory_type: 'norm',
      critic: 0.95,
    });

    const base = await activate({ q: query, top_k: 3 });
    expect(claimIds(base)).toEqual([normId, factId, taskId]);

    const resumed = await activate({ q: query, intent: 'resume_task', top_k: 3 });
    expect(resumed.intent).toBe('resume_task');
    expect(claimIds(resumed)[0]).toBe(taskId);
    expect(claimIds(resumed).indexOf(taskId)).toBeLessThan(claimIds(resumed).indexOf(normId));
    expect(claimIds(resumed)).toContain(factId);
  });

  it('POLICY_CHECK ranks norm policy hints above task and fact claims', async () => {
    const query = 'policy intent fixture';
    const taskId = await createClaim({
      text: `${query} pending rollout task`,
      kind: 'task',
      memory_type: 'working_state',
      critic: 0.95,
    });
    const factId = await createClaim({
      text: `${query} implementation note`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.9,
    });
    const normId = await createClaim({
      text: `${query} requires policy review`,
      kind: 'policy_hint',
      memory_type: 'norm',
      critic: 0.8,
    });

    const base = await activate({ q: query, top_k: 3 });
    expect(claimIds(base)).toEqual([taskId, factId, normId]);

    const policyCheck = await activate({ q: query, intent: 'policy_check', top_k: 3 });
    expect(policyCheck.intent).toBe('policy_check');
    expect(claimIds(policyCheck)[0]).toBe(normId);
    expect(claimIds(policyCheck).indexOf(normId)).toBeLessThan(
      claimIds(policyCheck).indexOf(taskId)
    );
    expect(claimIds(policyCheck).indexOf(normId)).toBeLessThan(
      claimIds(policyCheck).indexOf(factId)
    );
  });

  it('DESIGN_DECISION ranks knowledge above evidence', async () => {
    const query = 'design decision fixture';
    const evidenceId = await createClaim({
      text: `${query} reproduced stack trace and logs`,
      kind: 'fact',
      memory_type: 'evidence',
      critic: 0.95,
    });
    const procedureId = await createClaim({
      text: `${query} rollout procedure checklist`,
      kind: 'fact',
      memory_type: 'procedure',
      critic: 0.8,
    });
    const knowledgeId = await createClaim({
      text: `${query} architecture rationale and tradeoffs`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.82,
    });

    const base = await activate({ q: query, top_k: 3 });
    expect(claimIds(base)).toEqual([evidenceId, knowledgeId, procedureId]);

    const designDecision = await activate({ q: query, intent: 'design_decision', top_k: 3 });
    expect(designDecision.intent).toBe('design_decision');
    expect(claimIds(designDecision)[0]).toBe(knowledgeId);
    expect(claimIds(designDecision).indexOf(knowledgeId)).toBeLessThan(
      claimIds(designDecision).indexOf(evidenceId)
    );
    expect(claimIds(designDecision)).toEqual([knowledgeId, evidenceId, procedureId]);
  });

  it('DEBUG_INCIDENT prioritizes recent promoted claims above old facts', async () => {
    const query = 'debug incident fixture';
    const oldFactOne = await createClaim({
      text: `${query} old incident write-up`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 1.0,
      ageDays: 180,
    });
    const oldFactTwo = await createClaim({
      text: `${query} historical mitigation note`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.95,
      ageDays: 150,
    });
    const recentClaimId = await promoteObservations(
      [
        `${query} latest failure reproduced from operator notes`,
        `${query} fresh stack sample captured during investigation`,
      ],
      'debug incident promotion',
      0.75
    );

    const base = await activate({ q: query, top_k: 3 });
    expect(claimIds(base)).toEqual([oldFactOne, oldFactTwo, recentClaimId]);

    const debugIncident = await activate({ q: query, intent: 'debug_incident', top_k: 3 });
    expect(debugIncident.intent).toBe('debug_incident');
    expect(claimIds(debugIncident)[0]).toBe(recentClaimId);
    expect(claimIds(debugIncident).indexOf(recentClaimId)).toBeLessThan(
      claimIds(debugIncident).indexOf(oldFactOne)
    );
    expect(claimIds(debugIncident).indexOf(recentClaimId)).toBeLessThan(
      claimIds(debugIncident).indexOf(oldFactTwo)
    );
  });

  it('KIND FILTER returns only facts', async () => {
    const query = 'kind filter fixture';
    const factId = await createClaim({
      text: `${query} fact result`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.9,
    });
    await createClaim({
      text: `${query} task result`,
      kind: 'task',
      memory_type: 'working_state',
      critic: 0.95,
    });
    await createClaim({
      text: `${query} preference result`,
      kind: 'preference',
      memory_type: 'knowledge',
      critic: 0.85,
    });

    const filtered = await activate({ q: query, kind_filter: ['fact'], top_k: 10 });
    expect(claimIds(filtered)).toEqual([factId]);
    expect(filtered.claims_count).toBe(1);
    expect(filtered.claims.every((item) => item.claim.kind === 'fact')).toBe(true);
  });

  it('MEMORY_TYPE FILTER returns only knowledge claims', async () => {
    const query = 'memory type filter fixture';
    const knowledgeId = await createClaim({
      text: `${query} knowledge result`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.9,
    });
    await createClaim({
      text: `${query} procedure result`,
      kind: 'fact',
      memory_type: 'procedure',
      critic: 0.95,
    });
    await createClaim({
      text: `${query} norm result`,
      kind: 'policy_hint',
      memory_type: 'norm',
      critic: 0.85,
    });

    const filtered = await activate({
      q: query,
      memory_type_filter: ['knowledge'],
      top_k: 10,
    });
    expect(claimIds(filtered)).toEqual([knowledgeId]);
    expect(filtered.claims_count).toBe(1);
    expect(filtered.claims.every((item) => item.claim.memory_type === 'knowledge')).toBe(true);
  });

  it('COMBINED FILTERS return only the policy_hint norm intersection', async () => {
    const query = 'combined filter fixture';
    const intersectionId = await createClaim({
      text: `${query} approved policy constraint`,
      kind: 'policy_hint',
      memory_type: 'norm',
      critic: 0.7,
    });
    await createClaim({
      text: `${query} explanatory policy note`,
      kind: 'policy_hint',
      memory_type: 'knowledge',
      critic: 0.95,
    });
    await createClaim({
      text: `${query} implementation task`,
      kind: 'task',
      memory_type: 'working_state',
      critic: 0.98,
    });

    const filtered = await activate({
      q: query,
      intent: 'policy_check',
      kind_filter: ['policy_hint'],
      memory_type_filter: ['norm'],
      top_k: 10,
    });

    expect(filtered.intent).toBe('policy_check');
    expect(claimIds(filtered)).toEqual([intersectionId]);
    expect(filtered.claims[0]?.claim.kind).toBe('policy_hint');
    expect(filtered.claims[0]?.claim.memory_type).toBe('norm');
  });

  it('ACTIVE_CONTEXT_ITEMS persists score_breakdown, source_layer, and rank for each item', async () => {
    const query = 'active context persistence fixture';
    const projectTaskId = await createClaim({
      text: `${query} current task handoff`,
      kind: 'task',
      memory_type: 'working_state',
      scope: 'project',
      critic: 0.95,
    });
    const projectFactId = await createClaim({
      text: `${query} project decision`,
      kind: 'fact',
      memory_type: 'knowledge',
      scope: 'project',
      critic: 0.9,
    });
    const principleNormId = await createClaim({
      text: `${query} principle guardrail`,
      kind: 'policy_hint',
      memory_type: 'norm',
      scope: 'principle',
      critic: 0.8,
    });

    const response = await activate({
      q: query,
      intent: 'resume_task',
      top_k: 3,
      scope: ['project', 'principle'],
    });

    expect(claimIds(response)).toEqual([projectTaskId, projectFactId, principleNormId]);

    const rows = await getActiveContextItems(response.active_context_id);
    expect(rows).toHaveLength(3);

    const rowByClaimId = new Map(rows.map((row) => [row.claim_id, row]));
    response.claims.forEach((item, index) => {
      const row = rowByClaimId.get(item.claim.id);
      expect(row).toBeDefined();
      expect(row?.source_layer).toBe(item.source_layer);
      expect(row?.rank).toBe(index + 1);
      expect(row?.selection_reason).toContain(`rank=${index + 1}`);
      expect(row?.selection_reason).toContain('intent=resume_task');

      const breakdown = JSON.parse(row?.score_breakdown ?? '{}') as {
        score_final?: number;
        intent?: { boost?: number };
      };
      expect(breakdown.score_final).toBeGreaterThan(0);
      expect(breakdown.intent?.boost).toBeGreaterThanOrEqual(1);
    });
  });

  it('PAGINATION WITH FILTERS paginates only fact results', async () => {
    const query = 'pagination filter fixture';
    const expectedFactIds: string[] = [];

    for (let index = 0; index < 10; index++) {
      expectedFactIds.push(
        await createClaim({
          text: `${query} fact ${index}`,
          kind: 'fact',
          memory_type: 'knowledge',
          critic: 100 - index,
        })
      );
    }

    for (let index = 0; index < 10; index++) {
      await createClaim({
        text: `${query} task ${index}`,
        kind: 'task',
        memory_type: 'working_state',
        critic: 200 - index,
      });
    }

    const pageSizes: number[] = [];
    const collectedIds: string[] = [];
    let cursor: string | undefined;

    for (;;) {
      const page = await activate({
        q: query,
        kind_filter: ['fact'],
        top_k: 3,
        ...(cursor ? { cursor } : {}),
      });

      pageSizes.push(page.claims_count);
      collectedIds.push(...claimIds(page));
      expect(page.claims.every((item) => item.claim.kind === 'fact')).toBe(true);

      if (!page.has_more) {
        expect(page.next_cursor).toBeUndefined();
        break;
      }

      expect(page.next_cursor).toBeDefined();
      cursor = page.next_cursor;
    }

    expect(pageSizes).toEqual([3, 3, 3, 1]);
    expect(collectedIds).toEqual(expectedFactIds);
  });

  it('NO INTENT BACKWARD COMPAT keeps the v1 ranking when intent is omitted', async () => {
    const query = 'backward compat fixture';
    const factId = await createClaim({
      text: `${query} architecture note`,
      kind: 'fact',
      memory_type: 'knowledge',
      critic: 0.95,
    });
    const taskId = await createClaim({
      text: `${query} current task`,
      kind: 'task',
      memory_type: 'working_state',
      critic: 0.9,
    });
    const policyId = await createClaim({
      text: `${query} policy requirement`,
      kind: 'policy_hint',
      memory_type: 'norm',
      critic: 0.8,
    });

    const noIntent = await activate({ q: query, top_k: 3 });
    expect(noIntent.intent).toBeUndefined();
    expect(claimIds(noIntent)).toEqual([factId, taskId, policyId]);

    const policyCheck = await activate({ q: query, intent: 'policy_check', top_k: 3 });
    expect(claimIds(policyCheck)).toEqual([policyId, factId, taskId]);
  });
});

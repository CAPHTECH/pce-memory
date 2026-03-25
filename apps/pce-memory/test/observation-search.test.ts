import { beforeEach, describe, expect, it } from 'vitest';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { getConnection } from '../src/db/connection';
import { gcExpiredObservations } from '../src/store/observations';
import {
  applyPolicy,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

type ActivateResponse = {
  claims: Array<{
    claim: {
      id: string;
      observation_id?: string;
      source_record_type?: string;
      source_type?: string;
      content?: string;
      actor?: string | null;
      tags?: string[] | null;
      created_at?: string;
      expires_at?: string | null;
    };
    source_layer?: string;
    selection_reason?: string;
  }>;
  claims_count: number;
};

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  if (result.isError === true) {
    throw new Error(JSON.stringify(result.structuredContent ?? result.content ?? result, null, 2));
  }

  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
  await applyPolicy({ threshold: 0.0 });
});

async function createObservation(content: string, boundary_class?: 'public' | 'internal' | 'pii') {
  return expectSuccess(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      ...(boundary_class ? { boundary_class } : {}),
      extract: { mode: 'noop' },
    })
  ) as {
    observation_id: string;
    effective_boundary_class: 'public' | 'internal' | 'pii' | 'secret';
  };
}

async function activateWithObservations(args: {
  q?: string;
  intent?: 'resume_task' | 'debug_incident' | 'design_decision' | 'policy_check';
  include_observations?: boolean;
  top_k?: number;
}) {
  return expectSuccess(
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      ...(args.q ? { q: args.q } : {}),
      ...(args.intent ? { intent: args.intent } : {}),
      ...(args.include_observations !== undefined
        ? { include_observations: args.include_observations }
        : {}),
      top_k: args.top_k ?? 10,
    })
  ) as ActivateResponse;
}

async function setObservationCreatedAt(observationId: string, ageDays: number): Promise<void> {
  const conn = await getConnection();
  const createdAt = new Date(Date.now() - ageDays * 24 * 60 * 60 * 1000).toISOString();
  await conn.run('UPDATE observations SET created_at = $1 WHERE id = $2', [
    createdAt,
    observationId,
  ]);
}

describe('observation search via activate', () => {
  it('activate schema exposes include_observations', () => {
    const activateTool = TOOL_DEFINITIONS.find((tool) => tool.name === 'pce_memory_activate');
    const includeObservationsSchema = activateTool?.inputSchema?.properties
      ?.include_observations as { type?: string; default?: boolean } | undefined;

    expect(includeObservationsSchema?.type).toBe('boolean');
    expect(includeObservationsSchema?.default).toBe(false);
  });

  it('observe -> activate(include_observations=true) finds short-term observation', async () => {
    const content = 'flaky test debug hypothesis next step';
    const observation = await createObservation(content, 'internal');

    const activate = await activateWithObservations({
      q: 'flaky test debug',
      include_observations: true,
    });

    expect(activate.claims_count).toBe(1);
    expect(activate.claims[0]?.claim.id).toBe(observation.observation_id);
    expect(activate.claims[0]?.claim.observation_id).toBe(observation.observation_id);
    expect(activate.claims[0]?.claim.source_record_type).toBe('observation');
    expect(activate.claims[0]?.claim.source_type).toBe('chat');
    expect(activate.claims[0]?.claim.content).toBe(content);
    expect(activate.claims[0]?.source_layer).toBe('micro');
  });

  it('expired observations are excluded', async () => {
    const observation = await createObservation('expired deploy note', 'internal');
    const conn = await getConnection();
    await conn.run(
      "UPDATE observations SET expires_at = (CURRENT_TIMESTAMP - INTERVAL '1 day') WHERE id = $1",
      [observation.observation_id]
    );
    await gcExpiredObservations('scrub');

    const activate = await activateWithObservations({
      q: 'expired deploy',
      include_observations: true,
    });

    expect(activate.claims_count).toBe(0);
  });

  it('secret observations are excluded from activate results', async () => {
    const secretText = `sk-${'A'.repeat(30)}`;
    const observation = await createObservation(secretText, 'internal');

    expect(observation.effective_boundary_class).toBe('secret');

    const activate = await activateWithObservations({
      q: 'sk-AAAA',
      include_observations: true,
    });

    expect(activate.claims_count).toBe(0);
  });

  it('observations are ranked by recency with recent items first', async () => {
    const newer = await createObservation('deploy investigation recent note', 'internal');
    const older = await createObservation('deploy investigation older note', 'internal');
    await setObservationCreatedAt(older.observation_id, 5);

    const activate = await activateWithObservations({
      q: 'deploy investigation',
      include_observations: true,
    });

    expect(activate.claims.slice(0, 2).map((item) => item.claim.observation_id)).toEqual([
      newer.observation_id,
      older.observation_id,
    ]);
  });

  it('observation recall still works when activate intent is provided', async () => {
    const observation = await createObservation(
      'resume task baton handoff next action',
      'internal'
    );

    const activate = await activateWithObservations({
      q: 'resume task baton',
      intent: 'resume_task',
      include_observations: true,
    });

    expect(activate.claims[0]?.claim.observation_id).toBe(observation.observation_id);
    expect(activate.claims[0]?.selection_reason).toContain('intent=resume_task');
  });

  it('caps observation slots to 30% of top_k when durable claims are available', async () => {
    for (let index = 0; index < 10; index += 1) {
      expectSuccess(
        await upsertClaimViaTool({
          text: `issue 69 durable activation signal ${index}`,
          kind: 'fact',
          scope: 'project',
        })
      );
    }
    for (let index = 0; index < 90; index += 1) {
      await createObservation(`issue 69 noisy transient observation ${index}`, 'internal');
    }

    const activate = await activateWithObservations({
      q: 'issue 69 activation',
      include_observations: true,
      top_k: 20,
    });

    const observationCount = activate.claims.filter(
      (item) => item.claim.source_record_type === 'observation'
    ).length;

    expect(observationCount).toBeLessThanOrEqual(6);
    expect(activate.claims.slice(0, 10).every((item) => item.claim.observation_id === undefined)).toBe(
      true
    );
  });

  it('activate remains backward compatible without include_observations flag', async () => {
    const claim = expectSuccess(
      await upsertClaimViaTool({
        text: 'durable runbook note',
        kind: 'fact',
        scope: 'project',
      })
    ) as { id: string };
    await createObservation('durable runbook note transient scratchpad', 'internal');

    const activate = await activateWithObservations({
      q: 'durable runbook note',
    });

    expect(activate.claims_count).toBe(1);
    expect(activate.claims[0]?.claim.id).toBe(claim.id);
    expect(activate.claims[0]?.claim.observation_id).toBeUndefined();
  });
});

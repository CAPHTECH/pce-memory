import { beforeEach, describe, expect, it } from 'vitest';
import { getConnection } from '../src/db/connection';
import {
  applyPolicy,
  dispatchTool,
  resetRetrievalPlannerTestState,
  upsertClaimViaTool,
} from './helpers/retrievalPlannerTestUtils';

type ToolResponse = Awaited<ReturnType<typeof dispatchTool>>;
type ToolStructuredContent = NonNullable<ToolResponse['structuredContent']>;

type ObserveResult = {
  observation_id: string;
  effective_boundary_class?: string;
};

type DistillResult = {
  candidate_id: string;
  distilled_text: string;
  proposed_kind: string;
  proposed_scope: string;
  proposed_memory_type: string | null;
  proposed_boundary_class: string;
  status: string;
  invariant_check_results?: {
    source_counts?: {
      observations?: number;
      claims?: number;
      active_context_claims?: number;
    };
  };
};

type PromoteResult = {
  claim_id: string;
  is_new: boolean;
  promoted_from: string;
  rollback_token: string;
};

type RollbackResult = {
  rollback_id: string;
  superseded_claim_id: string;
};

type ActivateResult = {
  active_context_id: string;
  intent?: string;
  claims_count: number;
  claims: Array<{
    claim: {
      id: string;
      scope: string;
      boundary_class: string;
      kind: string;
      memory_type?: string | null;
    };
  }>;
};

type FeedbackResult = {
  id: string;
  claim_id: string;
  signal: string;
};

beforeEach(async () => {
  await resetRetrievalPlannerTestState();
});

function expectSuccess<T extends ToolStructuredContent>(result: ToolResponse): T {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent as T;
}

function expectValidationError(result: ToolResponse, message: string): void {
  expect(result.isError).toBe(true);
  expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
  expect(result.structuredContent?.error?.message).toContain(message);
}

function isoOffset(msOffset: number): string {
  return new Date(Date.now() + msOffset).toISOString();
}

function buildProvenance(
  offsetMs: number,
  note?: string
): {
  at: string;
  actor: string;
  note?: string;
} {
  return note
    ? { at: isoOffset(offsetMs), actor: 'claude', note }
    : { at: isoOffset(offsetMs), actor: 'claude' };
}

function extractClaimIds(result: ActivateResult): string[] {
  return result.claims.map((item) => item.claim.id);
}

async function observeRaw(
  content: string,
  extra: Record<string, unknown> = {}
): Promise<ObserveResult> {
  return expectSuccess<ObserveResult>(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      extract: { mode: 'noop' },
      ...extra,
    })
  );
}

async function distillFromObservations(
  observationIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: observationIds,
      ...extra,
    })
  );
}

async function distillFromClaims(
  claimIds: string[],
  extra: Record<string, unknown> = {}
): Promise<DistillResult> {
  return expectSuccess<DistillResult>(
    await dispatchTool('pce_memory_distill', {
      source_claim_ids: claimIds,
      ...extra,
    })
  );
}

async function promoteCandidate(
  candidateId: string,
  extra: Record<string, unknown> = {}
): Promise<PromoteResult> {
  return expectSuccess<PromoteResult>(
    await dispatchTool('pce_memory_promote', {
      candidate_id: candidateId,
      provenance: buildProvenance(-60_000),
      ...extra,
    })
  );
}

async function rollbackClaim(claimId: string, reason: string): Promise<RollbackResult> {
  return expectSuccess<RollbackResult>(
    await dispatchTool('pce_memory_rollback', {
      claim_id: claimId,
      reason,
      provenance: buildProvenance(-30_000, reason),
    })
  );
}

async function activateClaims(
  q: string,
  overrides: Record<string, unknown> = {}
): Promise<ActivateResult> {
  return expectSuccess<ActivateResult>(
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 10,
      q,
      ...overrides,
    })
  );
}

async function submitHelpfulFeedback(claimId: string): Promise<FeedbackResult> {
  return expectSuccess<FeedbackResult>(
    await dispatchTool('pce_memory_feedback', {
      claim_id: claimId,
      signal: 'helpful',
    })
  );
}

async function readClaimRow(claimId: string): Promise<
  | {
      scope: string;
      boundary_class: string;
      utility: number;
      confidence: number;
    }
  | undefined
> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT scope, boundary_class, utility, confidence FROM claims WHERE id = $1',
    [claimId]
  );
  const rows = reader.getRowObjects() as Array<{
    scope: string;
    boundary_class: string;
    utility: number;
    confidence: number;
  }>;
  return rows[0];
}

async function readFeedbackRow(
  feedbackId: string
): Promise<{ active_context_id: string | null } | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT active_context_id FROM feedback WHERE id = $1', [
    feedbackId,
  ]);
  const rows = reader.getRowObjects() as Array<{ active_context_id: string | null }>;
  return rows[0];
}

describe('promotion lifecycle e2e', () => {
  it('HAPPY PATH: policy_apply → observe → distill → promote → activate → rollback → activate excludes claim', async () => {
    await applyPolicy();

    const observation = await observeRaw('happy path promotion lifecycle marker');
    const distill = await distillFromObservations([observation.observation_id]);
    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved happy path candidate',
    });

    const activated = await activateClaims('happy path promotion lifecycle');
    expect(activated.claims_count).toBe(1);
    expect(extractClaimIds(activated)).toContain(promote.claim_id);

    const rollback = await rollbackClaim(promote.claim_id, 'happy path rollback');
    expect(rollback.superseded_claim_id).toBe(promote.claim_id);

    const afterRollback = await activateClaims('happy path promotion lifecycle');
    expect(afterRollback.claims_count).toBe(0);
  });

  it('MULTI-SOURCE DISTILL: combines 3 observations, promotes, and activates the promoted claim', async () => {
    await applyPolicy();

    const sources = await Promise.all([
      observeRaw('multi-source lifecycle alpha detail'),
      observeRaw('multi-source lifecycle beta detail'),
      observeRaw('multi-source lifecycle gamma detail'),
    ]);

    const distill = await distillFromObservations(sources.map((item) => item.observation_id));
    expect(distill.invariant_check_results?.source_counts?.observations).toBe(3);
    expect(distill.distilled_text).toContain('multi-source lifecycle alpha detail');
    expect(distill.distilled_text).toContain('multi-source lifecycle beta detail');
    expect(distill.distilled_text).toContain('multi-source lifecycle gamma detail');

    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved multi-source candidate',
    });
    const activated = await activateClaims('multi-source lifecycle');

    expect(extractClaimIds(activated)).toContain(promote.claim_id);
  });

  it('CLAIM-TO-CLAIM DISTILL: escalates project claims into principle scope and activates from principle', async () => {
    await applyPolicy();

    const first = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({
        text: 'scope escalation alpha project claim',
      })
    );
    const second = expectSuccess<{ id: string }>(
      await upsertClaimViaTool({
        text: 'scope escalation beta project claim',
      })
    );

    const distill = await distillFromClaims([first.id, second.id], {
      proposed_scope: 'principle',
      note: 'promote shared project guidance into principle scope',
    });
    expect(distill.proposed_scope).toBe('principle');

    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved principle escalation',
    });
    const claimRow = await readClaimRow(promote.claim_id);
    expect(claimRow?.scope).toBe('principle');

    const principleActivate = await activateClaims('scope escalation', {
      scope: ['principle'],
    });
    expect(extractClaimIds(principleActivate)).toContain(promote.claim_id);

    const projectActivate = await activateClaims('scope escalation', {
      scope: ['project'],
    });
    expect(extractClaimIds(projectActivate)).not.toContain(promote.claim_id);
  });

  it('BOUNDARY ESCALATION: mixed internal and pii observations distill to pii and respect activate boundary filters', async () => {
    await applyPolicy();

    const internalObservation = await observeRaw('boundary escalation retention sync internal', {
      boundary_class: 'internal',
    });
    const piiObservation = await observeRaw(
      'boundary escalation retention sync pii alice@example.com',
      {
        boundary_class: 'pii',
      }
    );

    expect(piiObservation.effective_boundary_class).toBe('pii');

    const distill = await distillFromObservations([
      internalObservation.observation_id,
      piiObservation.observation_id,
    ]);
    expect(distill.proposed_boundary_class).toBe('pii');

    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved pii escalation',
    });
    const claimRow = await readClaimRow(promote.claim_id);
    expect(claimRow?.boundary_class).toBe('pii');

    const answerTaskActivate = await activateClaims('boundary escalation retention sync');
    expect(answerTaskActivate.claims_count).toBe(0);

    const piiAllowedActivate = await activateClaims('boundary escalation retention sync', {
      allow: ['tool:contact-lookup'],
    });
    expect(extractClaimIds(piiAllowedActivate)).toContain(promote.claim_id);
  });

  it('REJECTION FLOW: promote rejects missing provenance, then succeeds when provenance is provided', async () => {
    await applyPolicy();

    const observation = await observeRaw('rejection flow provenance lifecycle');
    const distill = await distillFromObservations([observation.observation_id]);

    const rejectedPromote = await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
    });
    expectValidationError(rejectedPromote, 'provenance.at');

    const promote = await promoteCandidate(distill.candidate_id, {
      provenance: buildProvenance(-55_000, 'retry after validation failure'),
      review_note: 'approved after provenance retry',
    });
    const activated = await activateClaims('rejection flow provenance');

    expect(extractClaimIds(activated)).toContain(promote.claim_id);
  });

  it('DOUBLE ROLLBACK: second rollback attempt returns a validation error', async () => {
    await applyPolicy();

    const observation = await observeRaw('double rollback lifecycle check');
    const distill = await distillFromObservations([observation.observation_id]);
    const promote = await promoteCandidate(distill.candidate_id);

    const firstRollback = await rollbackClaim(promote.claim_id, 'first rollback');
    expect(firstRollback.superseded_claim_id).toBe(promote.claim_id);

    const secondRollback = await dispatchTool('pce_memory_rollback', {
      claim_id: promote.claim_id,
      reason: 'second rollback attempt',
      provenance: buildProvenance(-20_000, 'second rollback attempt'),
    });
    expectValidationError(secondRollback, 'already rolled back');
  });

  it('FEEDBACK AFTER PROMOTE: activate then helpful feedback increases the promoted claim utility', async () => {
    await applyPolicy();

    const observation = await observeRaw('feedback lifecycle utility growth');
    const distill = await distillFromObservations([observation.observation_id]);
    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved for feedback loop',
    });

    const beforeFeedback = await readClaimRow(promote.claim_id);
    expect(beforeFeedback).toBeDefined();

    const activated = await activateClaims('feedback lifecycle utility');
    expect(extractClaimIds(activated)).toContain(promote.claim_id);

    const feedback = await submitHelpfulFeedback(promote.claim_id);
    const afterFeedback = await readClaimRow(promote.claim_id);

    expect(afterFeedback?.utility ?? -Infinity).toBeGreaterThan(
      beforeFeedback?.utility ?? Infinity
    );

    const feedbackRow = await readFeedbackRow(feedback.id);
    expect(feedbackRow?.active_context_id).toBe(activated.active_context_id);
  });

  it('FULL LIFECYCLE: observe → distill → promote → activate(intent=resume_task) → feedback → rollback → activate again is empty', async () => {
    await applyPolicy();

    const observation = await observeRaw('resume lifecycle baton handoff');
    const distill = await distillFromObservations([observation.observation_id], {
      proposed_kind: 'task',
    });
    expect(distill.proposed_kind).toBe('task');
    expect(distill.proposed_memory_type).toBe('working_state');

    const promote = await promoteCandidate(distill.candidate_id, {
      review_note: 'approved full lifecycle candidate',
    });

    const activated = await activateClaims('resume lifecycle baton', {
      intent: 'resume_task',
    });
    expect(activated.intent).toBe('resume_task');
    expect(extractClaimIds(activated)).toContain(promote.claim_id);

    await submitHelpfulFeedback(promote.claim_id);
    await rollbackClaim(promote.claim_id, 'full lifecycle rollback');

    const afterRollback = await activateClaims('resume lifecycle baton', {
      intent: 'resume_task',
    });
    expect(afterRollback.claims_count).toBe(0);
  });
});

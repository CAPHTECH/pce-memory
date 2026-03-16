import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import { saveActiveContext } from '../src/store/activeContext';
import { recordFeedback } from '../src/store/feedback';
import { computeHealthReport } from '../src/store/health';

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

describe('computeHealthReport', () => {
  it('returns zero/default values for empty DB', async () => {
    const report = await computeHealthReport();

    expect(report.total_claims).toBe(0);
    expect(report.by_kind).toEqual({});
    expect(report.by_scope).toEqual({});
    expect(report.confidence_bands).toEqual({ high: 0, medium: 0, low: 0 });
    expect(report.feedback_summary.total).toBe(0);
    expect(report.duplicate_feedback_rate).toBe(0);
    expect(report.never_activated_ratio.overall).toBe(0);
  });

  it('correctly counts by_kind and by_scope after claims insertion', async () => {
    await upsertClaim({
      text: 'fact claim 1',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-fact-1',
    });
    await upsertClaim({
      text: 'fact claim 2',
      kind: 'fact',
      scope: 'principle',
      boundary_class: 'internal',
      content_hash: 'sha256:health-fact-2',
    });
    await upsertClaim({
      text: 'pref claim 1',
      kind: 'preference',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-pref-1',
    });

    const report = await computeHealthReport();

    expect(report.total_claims).toBe(3);
    expect(report.by_kind).toEqual({ fact: 2, preference: 1 });
    expect(report.by_scope).toEqual({ project: 2, principle: 1 });
  });

  it('correctly summarizes feedback after insertion', async () => {
    const { claim: c1 } = await upsertClaim({
      text: 'claim for feedback',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-fb-1',
    });

    await recordFeedback({ claim_id: c1.id, signal: 'helpful' });
    await recordFeedback({ claim_id: c1.id, signal: 'helpful' });
    await recordFeedback({ claim_id: c1.id, signal: 'harmful' });
    await recordFeedback({ claim_id: c1.id, signal: 'duplicate' });

    const report = await computeHealthReport();

    expect(report.feedback_summary.helpful).toBe(2);
    expect(report.feedback_summary.harmful).toBe(1);
    expect(report.feedback_summary.duplicate).toBe(1);
    expect(report.feedback_summary.outdated).toBe(0);
    expect(report.feedback_summary.total).toBe(4);
    expect(report.duplicate_feedback_rate).toBe(0.25);
  });

  it('Property: total_claims === sum(by_kind) === sum(by_scope)', async () => {
    // Insert diverse claims
    const kinds = ['fact', 'preference', 'task', 'policy_hint'] as const;
    const scopes = ['session', 'project', 'principle'] as const;
    let idx = 0;
    for (const kind of kinds) {
      for (const scope of scopes) {
        idx++;
        await upsertClaim({
          text: `claim ${idx} for ${kind} ${scope}`,
          kind,
          scope,
          boundary_class: 'internal',
          content_hash: `sha256:health-prop-${idx}`,
        });
      }
    }

    const report = await computeHealthReport();

    const sumByKind = Object.values(report.by_kind).reduce((a, b) => a + b, 0);
    const sumByScope = Object.values(report.by_scope).reduce((a, b) => a + b, 0);

    expect(report.total_claims).toBe(sumByKind);
    expect(report.total_claims).toBe(sumByScope);
    expect(report.total_claims).toBe(12); // 4 kinds * 3 scopes
  });

  it('correctly classifies confidence bands', async () => {
    const conn = await getConnection();

    // High confidence (>= 0.7)
    await upsertClaim({
      text: 'high conf',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:conf-high',
    });
    await conn.run("UPDATE claims SET confidence = 0.9 WHERE content_hash = 'sha256:conf-high'");

    // Medium confidence (0.3 <= x < 0.7)
    await upsertClaim({
      text: 'med conf',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:conf-med',
    });
    // Default confidence is 0.5, so this is already medium

    // Low confidence (< 0.3)
    await upsertClaim({
      text: 'low conf',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:conf-low',
    });
    await conn.run("UPDATE claims SET confidence = 0.1 WHERE content_hash = 'sha256:conf-low'");

    const report = await computeHealthReport();

    expect(report.confidence_bands.high).toBe(1);
    expect(report.confidence_bands.medium).toBe(1);
    expect(report.confidence_bands.low).toBe(1);
  });

  it('never_activated_ratio excludes claims that appeared in active_contexts', async () => {
    const { claim: c1 } = await upsertClaim({
      text: 'activated claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-act-1',
    });
    await upsertClaim({
      text: 'never activated claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-act-2',
    });

    // c1のみをactive_contextsに保存（Claim[]形式）
    await saveActiveContext({ id: 'ac_test_health', claims: [c1] });

    const report = await computeHealthReport();

    // 2 claims total, 1 activated → never_activated = 1/2 = 0.5
    expect(report.total_claims).toBe(2);
    expect(report.never_activated_ratio.overall).toBe(0.5);
  });

  it('never_activated_ratio is 1.0 when no claims have been activated', async () => {
    await upsertClaim({
      text: 'orphan claim',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-orphan-1',
    });

    const report = await computeHealthReport();

    expect(report.total_claims).toBe(1);
    expect(report.never_activated_ratio.overall).toBe(1.0);
  });

  it('never_activated_ratio is 0.0 when all claims have been activated', async () => {
    const { claim: c1 } = await upsertClaim({
      text: 'all activated',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:health-allact-1',
    });

    await saveActiveContext({ id: 'ac_test_all', claims: [c1] });

    const report = await computeHealthReport();

    expect(report.total_claims).toBe(1);
    expect(report.never_activated_ratio.overall).toBe(0.0);
  });
});

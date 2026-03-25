import { getConnection } from '../db/connection.js';

export interface HealthReport {
  total_claims: number;
  by_kind: Record<string, number>;
  by_scope: Record<string, number>;
  confidence_bands: { high: number; medium: number; low: number };
  last_positive_feedback_age: { recent_30d: number; stale_90d: number; dormant: number };
  duplicate_feedback_rate: number;
  never_activated_ratio: { overall: number; by_age_bucket: Record<string, number> };
  utility_distribution: { mean: number; median: number; p10: number; p90: number };
  feedback_summary: Record<string, number> & { total: number };
}

/**
 * 知識ベースの健全性レポートを集計する
 */
export async function computeHealthReport(): Promise<HealthReport> {
  const conn = await getConnection();

  // total_claims
  const totalResult = await conn.runAndReadAll('SELECT COUNT(*)::INTEGER AS cnt FROM claims');
  const totalClaims = (totalResult.getRowObjects() as { cnt: number }[])[0]?.cnt ?? 0;

  // by_kind
  const kindResult = await conn.runAndReadAll(
    'SELECT kind, COUNT(*)::INTEGER AS cnt FROM claims GROUP BY kind'
  );
  const byKind: Record<string, number> = {};
  for (const row of kindResult.getRowObjects() as { kind: string; cnt: number }[]) {
    byKind[row.kind] = row.cnt;
  }

  // by_scope
  const scopeResult = await conn.runAndReadAll(
    'SELECT scope, COUNT(*)::INTEGER AS cnt FROM claims GROUP BY scope'
  );
  const byScope: Record<string, number> = {};
  for (const row of scopeResult.getRowObjects() as { scope: string; cnt: number }[]) {
    byScope[row.scope] = row.cnt;
  }

  // confidence_bands
  const confResult = await conn.runAndReadAll(`
    SELECT
      COALESCE(SUM(CASE WHEN confidence >= 0.7 THEN 1 ELSE 0 END), 0)::INTEGER AS high,
      COALESCE(SUM(CASE WHEN confidence >= 0.3 AND confidence < 0.7 THEN 1 ELSE 0 END), 0)::INTEGER AS medium,
      COALESCE(SUM(CASE WHEN confidence < 0.3 THEN 1 ELSE 0 END), 0)::INTEGER AS low
    FROM claims
  `);
  const confRow = (
    confResult.getRowObjects() as { high: number; medium: number; low: number }[]
  )[0] ?? { high: 0, medium: 0, low: 0 };

  // last_positive_feedback_age
  const feedbackAgeResult = await conn.runAndReadAll(`
    SELECT
      COALESCE(SUM(CASE WHEN f.ts >= CURRENT_TIMESTAMP - INTERVAL '30 days' THEN 1 ELSE 0 END), 0)::INTEGER AS recent_30d,
      COALESCE(SUM(CASE WHEN f.ts >= CURRENT_TIMESTAMP - INTERVAL '90 days' AND f.ts < CURRENT_TIMESTAMP - INTERVAL '30 days' THEN 1 ELSE 0 END), 0)::INTEGER AS stale_90d,
      COALESCE(SUM(CASE WHEN f.ts < CURRENT_TIMESTAMP - INTERVAL '90 days' THEN 1 ELSE 0 END), 0)::INTEGER AS dormant
    FROM (
      SELECT claim_id, MAX(ts) AS ts
      FROM feedback
      WHERE signal = 'helpful'
      GROUP BY claim_id
    ) f
  `);
  const feedbackAgeRow = (
    feedbackAgeResult.getRowObjects() as {
      recent_30d: number;
      stale_90d: number;
      dormant: number;
    }[]
  )[0] ?? { recent_30d: 0, stale_90d: 0, dormant: 0 };

  // duplicate_feedback_rate
  const dupResult = await conn.runAndReadAll(`
    SELECT
      COALESCE(SUM(CASE WHEN signal = 'duplicate' THEN 1 ELSE 0 END), 0)::INTEGER AS dup_count,
      COALESCE(COUNT(*), 0)::INTEGER AS total_count
    FROM feedback
  `);
  const dupRow = (dupResult.getRowObjects() as { dup_count: number; total_count: number }[])[0] ?? {
    dup_count: 0,
    total_count: 0,
  };
  const duplicateFeedbackRate = dupRow.total_count > 0 ? dupRow.dup_count / dupRow.total_count : 0;

  // never_activated_ratio (claims that have never appeared in active_contexts)
  // active_contexts.claims は Claim[] の JSON配列: [{id, text, kind, ...}, ...]
  // By age bucket: 0-7d, 7-30d, 30-90d, 90d+
  const neverActivatedResult = await conn.runAndReadAll(`
    WITH activated_claim_ids AS (
      SELECT DISTINCT json_extract_string(je.value, '$.id') AS claim_id
      FROM active_contexts, json_each(active_contexts.claims::JSON) AS je
      WHERE json_extract_string(je.value, '$.id') IS NOT NULL
    ),
    claim_ages AS (
      SELECT
        c.id,
        CASE
          WHEN c.created_at >= CURRENT_TIMESTAMP - INTERVAL '7 days' THEN '0-7d'
          WHEN c.created_at >= CURRENT_TIMESTAMP - INTERVAL '30 days' THEN '7-30d'
          WHEN c.created_at >= CURRENT_TIMESTAMP - INTERVAL '90 days' THEN '30-90d'
          ELSE '90d+'
        END AS age_bucket,
        CASE WHEN NOT EXISTS (
          SELECT 1 FROM activated_claim_ids WHERE activated_claim_ids.claim_id = c.id
        ) THEN 1 ELSE 0 END AS never_activated
      FROM claims c
    )
    SELECT
      age_bucket,
      COUNT(*)::INTEGER AS total,
      COALESCE(SUM(never_activated), 0)::INTEGER AS never_count
    FROM claim_ages
    GROUP BY age_bucket
  `);
  const byAgeBucket: Record<string, number> = {};
  let totalNever = 0;
  let totalForRatio = 0;
  for (const row of neverActivatedResult.getRowObjects() as {
    age_bucket: string;
    total: number;
    never_count: number;
  }[]) {
    byAgeBucket[row.age_bucket] = row.total > 0 ? row.never_count / row.total : 0;
    totalNever += row.never_count;
    totalForRatio += row.total;
  }
  const overallNeverActivated = totalForRatio > 0 ? totalNever / totalForRatio : 0;

  // utility_distribution
  const utilResult = await conn.runAndReadAll(`
    SELECT
      COALESCE(AVG(utility), 0) AS mean,
      COALESCE(MEDIAN(utility), 0) AS median,
      COALESCE(PERCENTILE_CONT(0.1) WITHIN GROUP (ORDER BY utility), 0) AS p10,
      COALESCE(PERCENTILE_CONT(0.9) WITHIN GROUP (ORDER BY utility), 0) AS p90
    FROM claims
  `);
  const utilRow = (
    utilResult.getRowObjects() as { mean: number; median: number; p10: number; p90: number }[]
  )[0] ?? { mean: 0, median: 0, p10: 0, p90: 0 };

  // feedback_summary
  const fbSummaryResult = await conn.runAndReadAll(
    'SELECT signal, COUNT(*)::INTEGER AS cnt FROM feedback GROUP BY signal'
  );
  const feedbackSummary: Record<string, number> & { total: number } = {
    helpful: 0,
    harmful: 0,
    outdated: 0,
    duplicate: 0,
    completed: 0,
    total: 0,
  };
  for (const row of fbSummaryResult.getRowObjects() as { signal: string; cnt: number }[]) {
    feedbackSummary[row.signal] = row.cnt;
    feedbackSummary.total += row.cnt;
  }

  return {
    total_claims: totalClaims,
    by_kind: byKind,
    by_scope: byScope,
    confidence_bands: confRow,
    last_positive_feedback_age: feedbackAgeRow,
    duplicate_feedback_rate: duplicateFeedbackRate,
    never_activated_ratio: { overall: overallNeverActivated, by_age_bucket: byAgeBucket },
    utility_distribution: utilRow,
    feedback_summary: feedbackSummary,
  };
}

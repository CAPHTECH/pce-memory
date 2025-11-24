/**
 * Property-based Testing Arbitraries for PCE
 *
 * このファイルはfast-checkを使用したProperty-based Testingのための
 * Arbitraryジェネレーターを提供します。
 *
 * LDE原則に従い、すべてのBranded Typeに対応するArbitraryを定義します。
 *
 * @see https://github.com/dubzzz/fast-check
 */

import * as fc from 'fast-check';
import type { Brand } from 'io-ts';

/**
 * Branded ID Arbitrary Generator Factory
 *
 * Branded Typeに対応するArbitraryを生成します。
 *
 * @param prefix - ID接頭辞 (例: 'clm_', 'obs_')
 * @param tag - Brand tag (例: 'ClaimId', 'ObservationId')
 * @returns fc.Arbitrary<Brand<string, {readonly __brand: T}>>
 *
 * @example
 * const ClaimIdArb = brandedId('clm_', 'ClaimId');
 * fc.sample(ClaimIdArb, 3);
 * // => ['clm_1a2b3c4d', 'clm_5e6f7g8h', 'clm_9i0j1k2l']
 */
export function brandedId<T extends string>(
  prefix: string,
  _tag: T
): fc.Arbitrary<Brand<string, { readonly __brand: T }>> {
  return fc
    .hexaString({ minLength: 8, maxLength: 16 })
    .map((hex) => `${prefix}${hex}` as Brand<string, { readonly __brand: T }>);
}

/**
 * Core PCE Branded ID Arbitraries
 *
 * core-types.mdで定義されたすべてのBranded IDに対応します。
 */
export const ClaimIdArb = brandedId('clm_', 'ClaimId');
export const ObservationIdArb = brandedId('obs_', 'ObservationId');
export const ActiveContextIdArb = brandedId('ac_', 'ActiveContextId');
export const EntityIdArb = brandedId('ent_', 'EntityId');
export const RelationIdArb = brandedId('rel_', 'RelationId');
export const EvidenceIdArb = brandedId('evd_', 'EvidenceId');
export const FeedbackIdArb = brandedId('fb_', 'FeedbackId');

/**
 * PolicyVersion Arbitrary (SemVer)
 *
 * SemVer形式のPolicyVersionを生成します。
 *
 * @example
 * fc.sample(PolicyVersionArb, 3);
 * // => ['0.1.0', '1.2.3', '2.0.0']
 */
export const PolicyVersionArb = fc
  .tuple(fc.nat({ max: 10 }), fc.nat({ max: 20 }), fc.nat({ max: 50 }))
  .map(
    ([major, minor, patch]) =>
      `${major}.${minor}.${patch}` as Brand<string, { readonly __brand: 'PolicyVersion' }>
  );

/**
 * Scope Arbitrary
 *
 * PCEのスコープ (session, project, principle) を生成します。
 */
export const ScopeArb = fc.constantFrom('session', 'project', 'principle');

/**
 * BoundaryClass Arbitrary
 *
 * 境界クラス (public, internal, confidential, restricted) を生成します。
 */
export const BoundaryClassArb = fc.constantFrom('public', 'internal', 'confidential', 'restricted');

/**
 * ClaimKind Arbitrary
 *
 * 主張の種類 (fact, task, preference, policy_hint) を生成します。
 */
export const ClaimKindArb = fc.constantFrom('fact', 'task', 'preference', 'policy_hint');

/**
 * Timestamp Arbitrary (UNIX epoch seconds)
 *
 * 過去1年間のUNIXタイムスタンプを生成します。
 */
export const TimestampArb = fc.integer({
  min: Math.floor(Date.now() / 1000) - 365 * 24 * 3600, // 1年前
  max: Math.floor(Date.now() / 1000), // 現在
});

/**
 * Confidence/Utility/Quality Score Arbitrary
 *
 * [0, 1] 範囲のスコアを生成します。
 */
export const ScoreArb = fc.double({ min: 0, max: 1, noNaN: true });

/**
 * Observation Arbitrary
 *
 * Observationオブジェクトを生成します。
 *
 * @example
 * fc.sample(ObservationArb, 1);
 * // => [{ id: 'obs_1a2b3c', source: 'user_input', content: '...', ... }]
 */
export const ObservationArb = fc.record({
  id: ObservationIdArb,
  source: fc.constantFrom('user_input', 'tool_output', 'system_event', 'agent_action'),
  content: fc.lorem({ maxCount: 50 }),
  metadata: fc.option(fc.dictionary(fc.string(), fc.anything()), { nil: undefined }),
  ts: TimestampArb,
});

/**
 * Claim Arbitrary
 *
 * Claimオブジェクトを生成します（origin_observation_id必須）。
 */
export const ClaimArb = fc.record({
  id: ClaimIdArb,
  text: fc.lorem({ maxCount: 30 }),
  kind: ClaimKindArb,
  scope: ScopeArb,
  boundary_class: BoundaryClassArb,
  origin_observation_id: ObservationIdArb, // 必須
  quality: ScoreArb,
  confidence: ScoreArb,
  utility: ScoreArb,
  recency: ScoreArb,
  content_hash: fc.option(fc.hexaString({ minLength: 64, maxLength: 64 }), { nil: undefined }),
  created_at: TimestampArb,
  updated_at: TimestampArb,
});

/**
 * Boundary Arbitrary
 *
 * Boundaryオブジェクトを生成します。
 */
export const BoundaryArb = fc.record({
  scope: ScopeArb,
  boundary_classes: fc.array(BoundaryClassArb, { minLength: 1, maxLength: 4 }).map((arr) => new Set(arr)),
});

/**
 * Entity Arbitrary
 *
 * Entityオブジェクトを生成します。
 */
export const EntityArb = fc.record({
  id: EntityIdArb,
  type: fc.constantFrom('person', 'organization', 'resource', 'concept'),
  name: fc.lorem({ maxCount: 3 }),
  canonical_key: fc.option(fc.string(), { nil: undefined }),
  attrs: fc.option(fc.dictionary(fc.string(), fc.anything()), { nil: undefined }),
});

/**
 * Relation Arbitrary
 *
 * Relationオブジェクトを生成します。
 */
export const RelationArb = fc.record({
  id: RelationIdArb,
  src_id: EntityIdArb,
  dst_id: EntityIdArb,
  type: fc.constantFrom('REFERENCES', 'PART_OF', 'RELATED_TO', 'DEPENDS_ON'),
  props: fc.option(fc.dictionary(fc.string(), fc.anything()), { nil: undefined }),
  evidence_claim_id: fc.option(ClaimIdArb, { nil: undefined }),
});

/**
 * Feedback Arbitrary
 *
 * Feedbackオブジェクトを生成します。
 */
export const FeedbackArb = fc.record({
  id: FeedbackIdArb,
  claim_id: ClaimIdArb,
  ts: TimestampArb,
  signal: fc.constantFrom('helpful', 'harmful', 'outdated', 'duplicate'),
  score: fc.option(ScoreArb, { nil: undefined }),
});

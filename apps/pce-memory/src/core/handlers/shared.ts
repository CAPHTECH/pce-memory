/**
 * Shared utility functions and types for MCP Tool Handlers.
 *
 * Extracted from handlers.ts to enable modular handler files.
 */

import { allowTagMatches as boundaryAllowTagMatches } from '@pce/boundary';
import { computeContentHash } from '@pce/embeddings';
import type { BoundaryPolicy } from '@pce/policy-schemas';
import type { Claim, Provenance } from '../../store/claims.js';
import { findClaimsByIds } from '../../store/claims.js';
import { upsertEntity, linkClaimEntity } from '../../store/entities.js';
import type { EntityInput } from '../../store/entities.js';
import { upsertRelation } from '../../store/relations.js';
import type { RelationInput } from '../../store/relations.js';
import type { ClaimLinkType } from '../../store/claimLinks.js';
import { findOneHopClaimLinks } from '../../store/claimLinks.js';
import type { ErrorCode } from '../../domain/errors.js';
import type { DomainError } from '../../domain/errors.js';
import { validationError } from '../../domain/errors.js';
import { isValidClaimKind } from '../../domain/types.js';
import type { ActivateIntent, ClaimKind, ClaimStatus, MemoryType } from '../../domain/types.js';
import * as E from 'fp-ts/Either';
import { getPolicy, getStateType, canDoUpsert } from '../../state/memoryState.js';
import { isInActiveScope } from '../../state/layerScopeState.js';
import { safeJsonStringify } from '../../utils/serialization.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import type { ScoreBreakdown } from '../../store/rerank.js';

// ========== Validation Functions ==========
// (Previously in domain/validation.ts, now deleted — inlined here)

export const validateStringE = (
  field: string,
  value: unknown,
  maxLength: number
): E.Either<DomainError, string> => {
  if (typeof value !== 'string') {
    return E.left(validationError(`${field} must be a string`));
  }
  if (value.length === 0) {
    return E.left(validationError(`${field} cannot be empty`));
  }
  if (value.length > maxLength) {
    return E.left(validationError(`${field} exceeds maximum length of ${maxLength}`));
  }
  return E.right(value);
};

export const validateStringFields = (
  fields: Array<[string, unknown, number]>
): E.Either<DomainError, string[]> => {
  const results: string[] = [];
  for (const [field, value, maxLength] of fields) {
    const result = validateStringE(field, value, maxLength);
    if (E.isLeft(result)) {
      return result as E.Either<DomainError, string[]>;
    }
    results.push(result.right);
  }
  return E.right(results);
};

// ========== Type Definitions ==========

/**
 * MCP Tool Result型
 * structuredContent: MCP outputSchema対応のための構造化データ
 */
export type ToolResult = {
  content: Array<{ type: string; text: string }>;
  structuredContent?: Record<string, unknown>;
  isError?: boolean;
};

/**
 * 統一されたToolResult生成ヘルパー
 * content（後方互換性用テキスト）とstructuredContent（構造化データ）の両方を生成
 */
export function createToolResult<T extends Record<string, unknown>>(
  data: T,
  options: { isError?: boolean; useSafeStringify?: boolean } = {}
): ToolResult {
  const text = options.useSafeStringify ? safeJsonStringify(data) : JSON.stringify(data);
  // structuredContentもBigIntを含む可能性があるため、useSafeStringifyの場合は変換済みデータを使用
  const structuredData = options.useSafeStringify
    ? (JSON.parse(text) as Record<string, unknown>)
    : data;
  return {
    content: [{ type: 'text', text }],
    structuredContent: structuredData,
    ...(options.isError && { isError: true }),
  };
}

// ========== Utility Functions ==========

export function getUnknownFields(
  args: Record<string, unknown>,
  allowedFields: readonly string[]
): string[] {
  return Object.keys(args).filter((field) => !allowedFields.includes(field));
}

export function isLeapYear(year: number): boolean {
  return year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0);
}

export function getDaysInMonth(year: number, month: number): number {
  switch (month) {
    case 2:
      return isLeapYear(year) ? 29 : 28;
    case 4:
    case 6:
    case 9:
    case 11:
      return 30;
    default:
      return 31;
  }
}

export function isValidIsoDateTime(value: string): boolean {
  const match =
    /^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(\.\d{1,9})?(Z|([+-])(\d{2}):(\d{2}))$/.exec(
      value
    );
  if (!match) {
    return false;
  }

  const year = Number(match[1]);
  const month = Number(match[2]);
  const day = Number(match[3]);
  const hour = Number(match[4]);
  const minute = Number(match[5]);
  const second = Number(match[6]);
  const offsetHour = Number(match[9] ?? '0');
  const offsetMinute = Number(match[10] ?? '0');

  if (!Number.isInteger(year) || year < 0) return false;
  if (month < 1 || month > 12) return false;
  if (day < 1 || day > getDaysInMonth(year, month)) return false;
  if (hour < 0 || hour > 23) return false;
  if (minute < 0 || minute > 59) return false;
  if (second < 0 || second > 59) return false;
  if (offsetHour < 0 || offsetHour > 23) return false;
  if (offsetMinute < 0 || offsetMinute > 59) return false;

  return !Number.isNaN(Date.parse(value));
}

export function validateProvenanceAt(
  value: unknown
): { ok: true; value: string } | { ok: false; message: string } {
  if (typeof value !== 'string' || value.length === 0) {
    return { ok: false, message: 'provenance.at is required' };
  }
  if (!isValidIsoDateTime(value)) {
    return {
      ok: false,
      message: 'provenance.at must be a valid ISO8601 datetime with timezone',
    };
  }
  return { ok: true, value };
}

export function hasPathTraversal(value: string): boolean {
  const raw = value.replace(/\\/g, '/');
  const decoded = (() => {
    try {
      return decodeURIComponent(value).replace(/\\/g, '/');
    } catch {
      return raw;
    }
  })();
  const pattern = /(?:^|\/)\.\.(?:\/|$)/;
  return pattern.test(raw) || pattern.test(decoded);
}

export function err(code: ErrorCode, message: string, request_id: string) {
  return { error: { code, message }, request_id };
}

// Issue #30 Review: allowTagMatchesを@pce/boundaryからインポートして重複排除
// 後方互換性のためローカルエイリアスを維持
export const allowTagMatches = boundaryAllowTagMatches;

export function isAllowedByBoundary(allowList: string[], requestedAllow: string[]): boolean {
  return allowList.some((p) => requestedAllow.some((t) => allowTagMatches(p, t)));
}

export function getAllowedBoundaryClasses(
  policy: BoundaryPolicy,
  requestedAllow: string[]
): string[] {
  return Object.entries(policy.boundary_classes)
    .filter(([, boundary]) => isAllowedByBoundary(boundary.allow ?? [], requestedAllow))
    .map(([boundaryClass]) => boundaryClass);
}

export type DurableScope = 'project' | 'principle';
export type DurableBoundaryClass = 'public' | 'internal' | 'pii' | 'secret';

export const DEFAULT_PROMOTION_MAX_SOURCES = 64;
export const DEFAULT_PROMOTION_MAX_BYTES = 65_536;
export const DEFAULT_PROVENANCE_FUTURE_SKEW_MS = 300_000;
export const promotionLocks = new Map<string, Promise<void>>();

export const BOUNDARY_SEVERITY: Record<DurableBoundaryClass, number> = {
  public: 0,
  internal: 1,
  pii: 2,
  secret: 3,
};

export function isDurableScope(value: unknown): value is DurableScope {
  return value === 'project' || value === 'principle';
}

export function isDurableBoundaryClass(value: unknown): value is DurableBoundaryClass {
  return value === 'public' || value === 'internal' || value === 'pii' || value === 'secret';
}

export function getMostRestrictiveBoundary(
  boundaryClasses: DurableBoundaryClass[]
): DurableBoundaryClass {
  if (boundaryClasses.length === 0) {
    return 'internal';
  }
  return boundaryClasses.reduce<DurableBoundaryClass>(
    (current, candidate) =>
      BOUNDARY_SEVERITY[candidate] > BOUNDARY_SEVERITY[current] ? candidate : current,
    boundaryClasses[0]!
  );
}

export function inferDurableScope(kind: ClaimKind, memoryType?: MemoryType): DurableScope {
  if (kind === 'policy_hint' || memoryType === 'norm') {
    return 'principle';
  }
  return 'project';
}

export function inferMemoryTypeForKind(kind: ClaimKind): MemoryType | undefined {
  switch (kind) {
    case 'fact':
      return 'knowledge';
    case 'task':
      return 'working_state';
    case 'policy_hint':
      return 'norm';
    default:
      return undefined;
  }
}

export function mapScopeToLayer(scope: string): string {
  if (scope === 'principle') return 'macro';
  if (scope === 'project') return 'meso';
  return 'micro';
}

export function formatScore(value: number | undefined): string {
  return typeof value === 'number' && Number.isFinite(value) ? value.toFixed(4) : 'n/a';
}

export function buildSelectionReason(item: {
  score: number;
  claim: { kind: string; scope: string; memory_type?: string | null };
  score_breakdown?: {
    s_text?: number;
    s_vec?: number;
    intent?: { boost?: number };
  };
  source_layer?: string;
  rank: number;
  intent?: ActivateIntent;
  source?: 'search' | 'observation' | 'claim_link';
  link?: {
    via_claim_id: string;
    link_type: ClaimLinkType;
    confidence: number;
  };
}): string {
  const parts = [
    `rank=${item.rank}`,
    `layer=${item.source_layer ?? mapScopeToLayer(item.claim.scope)}`,
    `source=${item.source ?? 'search'}`,
    `score=${formatScore(item.score)}`,
    `kind=${item.claim.kind}`,
  ];

  if (item.claim.memory_type) {
    parts.push(`memory_type=${item.claim.memory_type}`);
  }
  if (item.intent) {
    parts.push(`intent=${item.intent}`);
  }
  if (item.score_breakdown) {
    parts.push(`s_text=${formatScore(item.score_breakdown.s_text)}`);
    parts.push(`s_vec=${formatScore(item.score_breakdown.s_vec)}`);
    if (item.score_breakdown.intent?.boost !== undefined) {
      parts.push(`intent_boost=${formatScore(item.score_breakdown.intent.boost)}`);
    }
  }
  if (item.link) {
    parts.push(`via_claim_id=${item.link.via_claim_id}`);
    parts.push(`link_type=${item.link.link_type}`);
    parts.push(`link_confidence=${formatScore(item.link.confidence)}`);
  }

  return parts.join('; ');
}

export const CLAIM_LINK_SCORE_PENALTY = 0.7;
export const CONNECTIVITY_SEED_MULTIPLIER = 3;

export type ActivateSearchItem = {
  claim: Claim;
  score: number;
  source_layer?: string;
  score_breakdown?: ScoreBreakdown;
  source?: 'search' | 'observation' | 'claim_link';
  link?: {
    id: string;
    via_claim_id: string;
    link_type: ClaimLinkType;
    confidence: number;
  };
};

export type FreshnessMetadata = {
  freshness: 'stale_candidate';
  newer_similar: string;
};

export type ActivateClaimResponse = Claim & Partial<FreshnessMetadata>;

export const OBSERVATION_SCORE_MERGE_HEADROOM = 0.98;
export const ACTIVATE_OBSERVATION_SLOT_FRACTION = 0.3;

export function getActivateItemTimestamp(item: ActivateSearchItem): number {
  const candidate = item.claim.updated_at ?? item.claim.created_at;
  const timestamp = new Date(candidate).getTime();
  return Number.isFinite(timestamp) ? timestamp : 0;
}

export function compareActivateSearchItems(
  left: ActivateSearchItem,
  right: ActivateSearchItem
): number {
  if (right.score !== left.score) {
    return right.score - left.score;
  }

  const timestampDiff = getActivateItemTimestamp(right) - getActivateItemTimestamp(left);
  if (timestampDiff !== 0) {
    return timestampDiff;
  }

  return right.claim.id.localeCompare(left.claim.id);
}

export function compareActivateSearchItemsWithFreshness(
  left: ActivateSearchItem,
  right: ActivateSearchItem,
  freshnessByClaimId: ReadonlyMap<string, FreshnessMetadata>
): number {
  const leftStale = freshnessByClaimId.has(left.claim.id);
  const rightStale = freshnessByClaimId.has(right.claim.id);
  if (leftStale !== rightStale) {
    return leftStale ? 1 : -1;
  }
  return compareActivateSearchItems(left, right);
}

export function augmentClaimWithFreshness(
  claim: Claim,
  freshnessByClaimId: ReadonlyMap<string, FreshnessMetadata>
): ActivateClaimResponse {
  const freshness = freshnessByClaimId.get(claim.id);
  if (!freshness) {
    return claim;
  }
  return {
    ...claim,
    freshness: freshness.freshness,
    newer_similar: freshness.newer_similar,
  };
}

export function maxActivateItemScore(items: ActivateSearchItem[]): number {
  return items.reduce((maxScore, item) => {
    return Number.isFinite(item.score) ? Math.max(maxScore, item.score) : maxScore;
  }, Number.NEGATIVE_INFINITY);
}

export function combineActivateScores(baseScore: number, additionalScore: number): number {
  const normalizedBase = Number.isFinite(baseScore) ? Math.max(0, Math.min(1, baseScore)) : 0;
  const normalizedAdditional = Number.isFinite(additionalScore)
    ? Math.max(0, Math.min(1, additionalScore))
    : 0;

  return normalizedBase + normalizedAdditional * (1 - normalizedBase);
}

export function getActivateExcludedWorkingStateStatuses(includeStaleTasks: boolean): ClaimStatus[] {
  return includeStaleTasks ? ['completed'] : ['completed', 'stale'];
}

export function claimMatchesActivateFilters(
  claim: Claim,
  input: {
    scopes: string[];
    boundaryClasses: string[];
    kindFilter?: ClaimKind[];
    memoryTypeFilter?: MemoryType[];
    excludedWorkingStateStatuses: ClaimStatus[];
  }
): boolean {
  if (!input.scopes.includes(claim.scope)) {
    return false;
  }
  if (!input.boundaryClasses.includes(claim.boundary_class)) {
    return false;
  }
  if (input.kindFilter && !input.kindFilter.includes(claim.kind as ClaimKind)) {
    return false;
  }
  if (
    input.memoryTypeFilter &&
    (claim.memory_type === null ||
      claim.memory_type === undefined ||
      !input.memoryTypeFilter.includes(claim.memory_type))
  ) {
    return false;
  }
  if (
    claim.memory_type === 'working_state' &&
    input.excludedWorkingStateStatuses.includes(claim.status)
  ) {
    return false;
  }
  return true;
}

export async function expandActivateResultsWithClaimLinks(
  durableResults: ActivateSearchItem[],
  input: {
    scopes: string[];
    boundaryClasses: string[];
    kindFilter?: ClaimKind[];
    memoryTypeFilter?: MemoryType[];
    excludedWorkingStateStatuses: ClaimStatus[];
  }
): Promise<ActivateSearchItem[]> {
  if (durableResults.length === 0) {
    return durableResults;
  }

  const merged = new Map<string, ActivateSearchItem>(
    durableResults.map((item) => [item.claim.id, { ...item, source: item.source ?? 'search' }])
  );
  const oneHopLinks = await findOneHopClaimLinks(durableResults.map((item) => item.claim.id));
  if (oneHopLinks.length === 0) {
    return [...merged.values()].sort(compareActivateSearchItems);
  }

  const connectedClaimIds = dedupeStrings(oneHopLinks.map((link) => link.connected_claim_id));
  const connectedClaims = await findClaimsByIds(connectedClaimIds);
  const connectedClaimsById = new Map(connectedClaims.map((claim) => [claim.id, claim]));
  const directResultsById = new Map(durableResults.map((item) => [item.claim.id, item]));

  for (const hop of oneHopLinks) {
    const connectedClaim = connectedClaimsById.get(hop.connected_claim_id);
    if (!connectedClaim) {
      continue;
    }
    if (!claimMatchesActivateFilters(connectedClaim, input)) {
      continue;
    }

    const viaResult = directResultsById.get(hop.seed_claim_id);
    if (!viaResult) {
      continue;
    }

    const score =
      viaResult.score * CLAIM_LINK_SCORE_PENALTY * Math.max(0, Math.min(1, hop.confidence));
    if (!Number.isFinite(score) || score <= 0) {
      continue;
    }

    const existing = merged.get(connectedClaim.id);
    const nextScore = existing === undefined ? score : combineActivateScores(existing.score, score);
    if (existing && existing.score >= nextScore) {
      continue;
    }

    merged.set(connectedClaim.id, {
      claim: connectedClaim,
      score: nextScore,
      source_layer: existing?.source_layer ?? mapScopeToLayer(connectedClaim.scope),
      source: 'claim_link',
      link: {
        id: hop.link_id,
        via_claim_id: hop.seed_claim_id,
        link_type: hop.link_type,
        confidence: Number(hop.confidence.toFixed(4)),
      },
    });
  }

  return [...merged.values()].sort(compareActivateSearchItems);
}

export function normalizeObservationScoresForActivate(
  durableResults: ActivateSearchItem[],
  observationResults: ActivateSearchItem[]
): ActivateSearchItem[] {
  if (durableResults.length === 0 || observationResults.length === 0) {
    return observationResults;
  }

  const maxDurableScore = maxActivateItemScore(durableResults);
  const maxObservationScore = maxActivateItemScore(observationResults);
  if (!(maxDurableScore > 0) || !(maxObservationScore > 0)) {
    return observationResults;
  }

  const scale = (maxDurableScore * OBSERVATION_SCORE_MERGE_HEADROOM) / maxObservationScore;
  if (!Number.isFinite(scale) || scale >= 1) {
    return observationResults;
  }

  return observationResults.map((item) => ({
    ...item,
    score: item.score * scale,
    source: item.source ?? 'observation',
  }));
}

export function getActivateObservationSlotCap(topK: number): number {
  return Math.max(0, Math.floor(topK * ACTIVATE_OBSERVATION_SLOT_FRACTION));
}

export function ensureClaimLinkPresence(
  pageResults: ActivateSearchItem[],
  allResults: ActivateSearchItem[],
  topK: number
): ActivateSearchItem[] {
  if (topK < 2 || pageResults.some((item) => item.source === 'claim_link')) {
    return pageResults;
  }

  const fallbackClaimLink = allResults.find(
    (item) =>
      item.source === 'claim_link' &&
      !pageResults.some((pageItem) => pageItem.claim.id === item.claim.id)
  );
  if (!fallbackClaimLink) {
    return pageResults;
  }

  const replacementIndex = (() => {
    for (let index = pageResults.length - 1; index >= 0; index--) {
      if (pageResults[index]?.source !== 'claim_link') {
        return index;
      }
    }
    return -1;
  })();
  if (replacementIndex < 0) {
    return pageResults;
  }

  const nextPage = [...pageResults];
  nextPage[replacementIndex] = fallbackClaimLink;
  return nextPage.sort(compareActivateSearchItems);
}

export function pageActivateResultsWithObservationCap(input: {
  durableResults: ActivateSearchItem[];
  observationResults: ActivateSearchItem[];
  topK: number;
  cursor?: string;
}): {
  searchResults: ActivateSearchItem[];
  nextCursor: string | undefined;
  hasMore: boolean;
} {
  const durableResults = [...input.durableResults].sort(compareActivateSearchItems);
  const observationResults = [...input.observationResults].sort(compareActivateSearchItems);
  const observationSlotCap = getActivateObservationSlotCap(input.topK);

  let durableIndex = 0;
  let observationIndex = 0;

  if (input.cursor !== undefined) {
    const durableCursorIndex = durableResults.findIndex((item) => item.claim.id === input.cursor);
    if (durableCursorIndex >= 0) {
      durableIndex = durableCursorIndex + 1;
    } else {
      const observationCursorIndex = observationResults.findIndex(
        (item) => item.claim.id === input.cursor
      );
      if (observationCursorIndex >= 0) {
        durableIndex = durableResults.length;
        observationIndex = observationCursorIndex + 1;
      }
    }
  }

  const durablePage = durableResults.slice(durableIndex, durableIndex + input.topK);
  const remainingSlots = Math.max(0, input.topK - durablePage.length);
  const observationPage = observationResults.slice(
    observationIndex,
    observationIndex + Math.min(observationSlotCap, remainingSlots)
  );

  const allResults = [...durableResults, ...observationResults].sort(compareActivateSearchItems);
  const searchResults = ensureClaimLinkPresence(
    [...durablePage, ...observationPage],
    allResults,
    input.topK
  );
  const nextDurableIndex = durableIndex + durablePage.length;
  const nextObservationIndex = observationIndex + observationPage.length;
  const hasMore =
    nextDurableIndex < durableResults.length ||
    (observationSlotCap > 0 && nextObservationIndex < observationResults.length);
  const nextCursor =
    hasMore && searchResults.length > 0
      ? searchResults[searchResults.length - 1]!.claim.id
      : undefined;

  return {
    searchResults,
    nextCursor,
    hasMore,
  };
}

export function pageActivateResults(input: {
  results: ActivateSearchItem[];
  topK: number;
  cursor?: string;
}): {
  searchResults: ActivateSearchItem[];
  nextCursor: string | undefined;
  hasMore: boolean;
} {
  const results = [...input.results].sort(compareActivateSearchItems);
  let startIndex = 0;
  if (input.cursor !== undefined) {
    const cursorIndex = results.findIndex((item) => item.claim.id === input.cursor);
    if (cursorIndex >= 0) {
      startIndex = cursorIndex + 1;
    }
  }

  const searchResults = ensureClaimLinkPresence(
    results.slice(startIndex, startIndex + input.topK),
    results,
    input.topK
  );
  const hasMore = startIndex + searchResults.length < results.length;
  const nextCursor =
    hasMore && searchResults.length > 0
      ? searchResults[searchResults.length - 1]!.claim.id
      : undefined;

  return {
    searchResults,
    nextCursor,
    hasMore,
  };
}

export function mapDurableScopeToTargetLayer(scope: DurableScope): 'meso' | 'macro' {
  return scope === 'principle' ? 'macro' : 'meso';
}

export function dedupeStrings(values: string[]): string[] {
  const seen = new Set<string>();
  const deduped: string[] = [];
  for (const value of values) {
    if (seen.has(value)) continue;
    seen.add(value);
    deduped.push(value);
  }
  return deduped;
}

export function readPositiveIntEnv(name: string, fallback: number): number {
  const rawValue = Number(process.env[name] ?? String(fallback));
  return Number.isFinite(rawValue) && rawValue > 0 ? Math.floor(rawValue) : fallback;
}

export function readNonNegativeIntEnv(name: string, fallback: number): number {
  const rawValue = Number(process.env[name] ?? String(fallback));
  return Number.isFinite(rawValue) && rawValue >= 0 ? Math.floor(rawValue) : fallback;
}

export async function acquirePromotionLock(key: string): Promise<() => void> {
  const previous = promotionLocks.get(key) ?? Promise.resolve();
  let release!: () => void;
  const current = new Promise<void>((resolve) => {
    release = resolve;
  });
  const next = previous.then(() => current);
  promotionLocks.set(key, next);
  await previous;

  return () => {
    release();
    if (promotionLocks.get(key) === next) {
      promotionLocks.delete(key);
    }
  };
}

export function parseJsonObject<T>(value: string | null | undefined, fallback: T): T {
  if (!value) {
    return fallback;
  }
  try {
    return JSON.parse(value) as T;
  } catch {
    return fallback;
  }
}

export function validateRequiredProvenance(
  provenance: unknown
): { ok: true; value: Provenance } | { ok: false; message: string } {
  if (typeof provenance !== 'object' || provenance === null) {
    return { ok: false, message: 'provenance.at is required' };
  }
  const candidate = provenance as Provenance;
  const validatedAt = validateProvenanceAt(candidate.at);
  if (!validatedAt.ok) {
    return validatedAt;
  }
  const atMs = Date.parse(candidate.at);
  if (Number.isNaN(atMs)) {
    return { ok: false, message: 'provenance.at must be a valid ISO 8601 timestamp' };
  }
  const allowedFutureSkewMs = readNonNegativeIntEnv(
    'PCE_PROVENANCE_FUTURE_SKEW_MS',
    DEFAULT_PROVENANCE_FUTURE_SKEW_MS
  );
  if (atMs > Date.now() + allowedFutureSkewMs) {
    return { ok: false, message: 'provenance.at cannot be in the future' };
  }
  return { ok: true, value: { ...candidate, at: new Date(atMs).toISOString() } };
}

export function resolveObservationSourceText(input: {
  content?: string | null;
  content_digest: string;
}): string {
  if (typeof input.content === 'string' && input.content.trim().length > 0) {
    return input.content;
  }
  return input.content_digest;
}

export function resolveClaimSourceText(input: { text: string; content_hash: string }): string {
  if (typeof input.text === 'string' && input.text.trim().length > 0) {
    return input.text;
  }
  return input.content_hash;
}

export function getPromotionCandidateConflictMessage(
  candidate: {
    distilled_text: string;
    proposed_kind: string;
    proposed_scope: string;
    proposed_boundary_class: string;
    proposed_memory_type?: MemoryType | null;
  },
  claim: Claim
): string | null {
  const candidateMemoryType = candidate.proposed_memory_type ?? null;
  const claimMemoryType = claim.memory_type ?? null;

  // Text mismatch is always a true collision
  if (claim.text !== candidate.distilled_text) {
    return 'candidate_hash collides with an existing claim that has different text';
  }

  // Kind and memory_type mismatches represent fundamentally different classifications
  if (claim.kind !== candidate.proposed_kind || claimMemoryType !== candidateMemoryType) {
    return 'candidate_hash collides with an existing claim that has different text or metadata';
  }

  // Scope and boundary_class differences are allowed:
  // - scope elevation (project -> principle) is a legitimate workflow
  // - boundary escalation (public -> internal) follows monotonicity
  return null;
}

// ========== Upsert Helper Functions ==========

/**
 * Upsertの入力バリデーション
 * 状態検証、レート制限、フィールド検証を実行
 */
export interface UpsertValidationResult {
  isValid: boolean;
  errorResponse?: ToolResult;
  resolvedHash?: string; // Auto-generated or validated content_hash
}

export async function validateUpsertInput(
  args: {
    text: string | undefined;
    kind: string | undefined;
    scope: string | undefined;
    boundary_class: string | undefined;
    content_hash: string | undefined;
  },
  scopeId: string,
  reqId: string,
  traceId: string
): Promise<UpsertValidationResult> {
  const { text, kind, scope, boundary_class, content_hash } = args;

  // 状態検証
  if (!canDoUpsert()) {
    const error = stateError('PolicyApplied or HasClaims or Ready', getStateType());
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!isInActiveScope(scopeId)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('STATE_ERROR', 'scope not active', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!(await checkAndConsume('tool'))) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!text || !kind || !scope || !boundary_class) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'missing fields', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  const fieldsResult = validateStringFields([
    ['text', text, 5000],
    ['kind', kind, 128],
    ['scope', scope, 128],
    ['boundary_class', boundary_class, 128],
  ]);
  if (E.isLeft(fieldsResult)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', fieldsResult.left.message, reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!isValidClaimKind(kind)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown kind', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (scope === 'session') {
    return {
      isValid: false,
      errorResponse: createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            "scope 'session' is no longer accepted by pce_memory_upsert; use pce_memory_observe for session-scoped working context",
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      ),
    };
  }

  if (!isDurableScope(scope)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown scope', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (!isDurableBoundaryClass(boundary_class)) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown boundary_class', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  const policy = getPolicy();
  if (!policy.boundary_classes[boundary_class]) {
    return {
      isValid: false,
      errorResponse: createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown boundary_class', reqId), trace_id: traceId },
        { isError: true }
      ),
    };
  }

  if (boundary_class === 'secret') {
    return {
      isValid: false,
      errorResponse: createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            "boundary_class 'secret' is rejected by default for pce_memory_upsert; use pce_memory_observe for secret material",
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      ),
    };
  }

  // content_hash処理: 未指定時は自動生成、指定時は検証
  const computedHash = `sha256:${computeContentHash(text)}`;
  let resolvedHash: string;

  if (content_hash) {
    // 指定時: 一致検証（改竄防止）
    if (content_hash !== computedHash) {
      return {
        isValid: false,
        errorResponse: createToolResult(
          {
            ...err(
              'VALIDATION_ERROR',
              'content_hash mismatch: provided hash does not match computed hash for text',
              reqId
            ),
            trace_id: traceId,
          },
          { isError: true }
        ),
      };
    }
    resolvedHash = content_hash;
  } else {
    // 未指定時: 自動生成
    resolvedHash = computedHash;
  }

  return { isValid: true, resolvedHash };
}

/**
 * Graph Memory（Entity/Relation）の処理
 * 新規Claimに対してのみentities/relationsを登録
 */
export interface GraphMemoryError {
  id: string;
  message: string;
}

export interface GraphMemoryResult {
  entityCount: number;
  entityErrors: GraphMemoryError[];
  relationCount: number;
  relationErrors: GraphMemoryError[];
}

export async function processGraphMemory(
  claimId: string,
  isNew: boolean,
  entities: EntityInput[] | undefined,
  relations: RelationInput[] | undefined
): Promise<GraphMemoryResult> {
  let entityCount = 0;
  const entityErrors: GraphMemoryError[] = [];
  let relationCount = 0;
  const relationErrors: GraphMemoryError[] = [];

  if (isNew && entities && Array.isArray(entities)) {
    for (const entity of entities) {
      try {
        await upsertEntity(entity);
        await linkClaimEntity(claimId, entity.id);
        entityCount++;
      } catch (e: unknown) {
        entityErrors.push({
          id: entity.id,
          message: e instanceof Error ? e.message : String(e),
        });
      }
    }
  }

  if (isNew && relations && Array.isArray(relations)) {
    for (const relation of relations) {
      try {
        await upsertRelation(relation);
        relationCount++;
      } catch (e: unknown) {
        relationErrors.push({
          id: relation.id,
          message: e instanceof Error ? e.message : String(e),
        });
      }
    }
  }

  return { entityCount, entityErrors, relationCount, relationErrors };
}

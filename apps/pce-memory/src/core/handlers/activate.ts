/**
 * handleActivate – build active context via hybrid search
 */

import {
  createToolResult,
  err,
  type ToolResult,
  getAllowedBoundaryClasses,
  mapScopeToLayer,
  buildSelectionReason,
  type ActivateSearchItem,
  type FreshnessMetadata,
  augmentClaimWithFreshness,
  compareActivateSearchItemsWithFreshness,
  expandActivateResultsWithClaimLinks,
  normalizeObservationScoresForActivate,
  getActivateExcludedWorkingStateStatuses,
  pageActivateResultsWithObservationCap,
  pageActivateResults,
  CONNECTIVITY_SEED_MULTIPLIER,
} from './shared.js';

import { markStaleWorkingStateClaims, recordClaimRetrievals } from '../../store/claims.js';
import type { Claim } from '../../store/claims.js';
import { hybridSearchWithScores, findNewerSimilarClaims } from '../../store/hybridSearch.js';
import type { TopologyEdgePolicyEntry } from '../../store/search/types.js';
import { resolveTopologyConfig } from '../../store/search/types.js';
import { collectMaintenanceHints } from '../../store/maintenance.js';
import { searchObservationsWithScores } from '../../store/observations.js';
import { getEvidenceForClaims } from '../../store/evidence.js';
import type { Evidence } from '../../store/evidence.js';
import { saveActiveContext, saveActiveContextItems } from '../../store/activeContext.js';
import { appendLog } from '../../store/logs.js';
import { checkAndConsume } from '../../store/rate.js';
import { stateError } from '../../domain/stateMachine.js';
import {
  ACTIVATE_INTENTS,
  CLAIM_KINDS,
  MEMORY_TYPES,
  isValidActivateIntent,
  isValidClaimKind,
  isValidMemoryType,
} from '../../domain/types.js';
import type { ActivateIntent, ClaimKind, MemoryType } from '../../domain/types.js';
import {
  getMaintenancePolicy,
  getPolicy,
  getRetrievalPolicy,
  getPolicyVersion,
  getStateType,
  canDoActivate,
  transitionToReady,
} from '../../state/memoryState.js';

export async function handleActivate(args: Record<string, unknown>): Promise<ToolResult> {
  const {
    scope,
    allow,
    top_k,
    q,
    cursor,
    include_meta,
    include_observations,
    include_stale_tasks,
    intent,
    kind_filter,
    memory_type_filter,
    debug_disable_graph_presence_injection,
  } = args as {
    scope?: unknown;
    allow?: unknown;
    top_k?: number;
    q?: string;
    cursor?: string;
    include_meta?: boolean;
    include_observations?: unknown;
    include_stale_tasks?: unknown;
    intent?: unknown;
    kind_filter?: unknown;
    memory_type_filter?: unknown;
    debug_disable_graph_presence_injection?: unknown;
  };
  const reqId = crypto.randomUUID();
  const traceId = crypto.randomUUID();
  try {
    const includeObservations = include_observations === true;
    const activateAllowed =
      canDoActivate() || (includeObservations && getStateType() === 'PolicyApplied');

    if (!activateAllowed) {
      const expectedState = includeObservations
        ? 'PolicyApplied or HasClaims or Ready'
        : 'HasClaims or Ready';
      const error = stateError(expectedState, getStateType());
      return createToolResult(
        { ...err('STATE_ERROR', error.message, reqId), trace_id: traceId },
        { isError: true }
      );
    }

    if (!(await checkAndConsume('activate'))) {
      return createToolResult(
        { ...err('RATE_LIMIT', 'rate limit exceeded', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (!Array.isArray(scope) || !Array.isArray(allow)) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'scope/allow must be arrays', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    const invalidScope = scope.some(
      (s: string) => !['session', 'project', 'principle'].includes(s)
    );
    if (invalidScope) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'unknown scope', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (allow.some((a: unknown) => typeof a !== 'string')) {
      return createToolResult(
        { ...err('VALIDATION_ERROR', 'allow must be string[]', reqId), trace_id: traceId },
        { isError: true }
      );
    }
    if (typeof top_k === 'number' && (!Number.isInteger(top_k) || top_k < 1 || top_k > 50)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'top_k must be an integer between 1 and 50', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (include_observations !== undefined && typeof include_observations !== 'boolean') {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'include_observations must be boolean', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (include_stale_tasks !== undefined && typeof include_stale_tasks !== 'boolean') {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', 'include_stale_tasks must be boolean', reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (
      debug_disable_graph_presence_injection !== undefined &&
      typeof debug_disable_graph_presence_injection !== 'boolean'
    ) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            'debug_disable_graph_presence_injection must be boolean',
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (intent !== undefined && !isValidActivateIntent(intent)) {
      return createToolResult(
        {
          ...err('VALIDATION_ERROR', `intent must be one of ${ACTIVATE_INTENTS.join('|')}`, reqId),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (
      kind_filter !== undefined &&
      (!Array.isArray(kind_filter) || kind_filter.some((value) => !isValidClaimKind(value)))
    ) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            `kind_filter must be ClaimKind[] (${CLAIM_KINDS.join('|')})`,
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }
    if (
      memory_type_filter !== undefined &&
      (!Array.isArray(memory_type_filter) ||
        memory_type_filter.some((value) => !isValidMemoryType(value)))
    ) {
      return createToolResult(
        {
          ...err(
            'VALIDATION_ERROR',
            `memory_type_filter must be MemoryType[] (${MEMORY_TYPES.join('|')})`,
            reqId
          ),
          trace_id: traceId,
        },
        { isError: true }
      );
    }

    const policy = getPolicy();
    const retrievalPolicy = getRetrievalPolicy();
    const maintenancePolicy = getMaintenancePolicy();
    const hybridPolicy = retrievalPolicy.hybrid ?? {};
    const allowTags = allow as string[];
    const allowedBoundaryClasses = getAllowedBoundaryClasses(policy, allowTags);
    const resolvedIntent = intent as ActivateIntent | undefined;
    const resolvedKindFilter = kind_filter as ClaimKind[] | undefined;
    const resolvedMemoryTypeFilter = memory_type_filter as MemoryType[] | undefined;
    const includeStaleTasks = include_stale_tasks === true;
    const resolvedTopK =
      top_k ??
      (typeof hybridPolicy.k_final === 'number' && Number.isFinite(hybridPolicy.k_final)
        ? Math.max(1, Math.floor(hybridPolicy.k_final))
        : 12);

    await markStaleWorkingStateClaims();

    const searchConfig = {
      boundaryClasses: allowedBoundaryClasses,
      ...(resolvedIntent ? { intent: resolvedIntent } : {}),
      ...(resolvedKindFilter ? { kindFilter: resolvedKindFilter } : {}),
      ...(resolvedMemoryTypeFilter ? { memoryTypeFilter: resolvedMemoryTypeFilter } : {}),
      excludedWorkingStateStatuses: getActivateExcludedWorkingStateStatuses(includeStaleTasks),
      includeBreakdown: true,
      ...(typeof hybridPolicy.alpha === 'number' ? { alpha: hybridPolicy.alpha } : {}),
      ...(typeof hybridPolicy.threshold === 'number' ? { threshold: hybridPolicy.threshold } : {}),
      ...(typeof hybridPolicy.k_txt === 'number' ? { kText: hybridPolicy.k_txt } : {}),
      ...(typeof hybridPolicy.k_vec === 'number' ? { kVec: hybridPolicy.k_vec } : {}),
      ...(hybridPolicy.mmr
        ? {
            mmr: {
              enabled: hybridPolicy.mmr.enabled === true,
              ...(typeof hybridPolicy.mmr.lambda === 'number'
                ? { lambda: hybridPolicy.mmr.lambda }
                : {}),
              ...(typeof hybridPolicy.mmr.max_candidates === 'number'
                ? { maxCandidates: hybridPolicy.mmr.max_candidates }
                : {}),
            },
          }
        : {}),
      ...(hybridPolicy.query_expansion
        ? {
            queryExpansion: {
              enabled: hybridPolicy.query_expansion.enabled === true,
              ...(typeof hybridPolicy.query_expansion.max_seed_entities === 'number'
                ? { maxSeedEntities: hybridPolicy.query_expansion.max_seed_entities }
                : {}),
              ...(typeof hybridPolicy.query_expansion.max_related_entities === 'number'
                ? { maxRelatedEntities: hybridPolicy.query_expansion.max_related_entities }
                : {}),
              ...(typeof hybridPolicy.query_expansion.max_expansion_terms === 'number'
                ? { maxExpansionTerms: hybridPolicy.query_expansion.max_expansion_terms }
                : {}),
            },
          }
        : {}),
      ...(hybridPolicy.feedback_boost
        ? {
            feedbackBoost: {
              enabled: hybridPolicy.feedback_boost.enabled === true,
              ...(typeof hybridPolicy.feedback_boost.helpful_weight === 'number'
                ? { helpfulWeight: hybridPolicy.feedback_boost.helpful_weight }
                : {}),
              ...(typeof hybridPolicy.feedback_boost.harmful_weight === 'number'
                ? { harmfulWeight: hybridPolicy.feedback_boost.harmful_weight }
                : {}),
              ...(typeof hybridPolicy.feedback_boost.outdated_weight === 'number'
                ? { outdatedWeight: hybridPolicy.feedback_boost.outdated_weight }
                : {}),
              ...(typeof hybridPolicy.feedback_boost.duplicate_weight === 'number'
                ? { duplicateWeight: hybridPolicy.feedback_boost.duplicate_weight }
                : {}),
              ...(typeof hybridPolicy.feedback_boost.min_multiplier === 'number'
                ? { minMultiplier: hybridPolicy.feedback_boost.min_multiplier }
                : {}),
              ...(typeof hybridPolicy.feedback_boost.max_multiplier === 'number'
                ? { maxMultiplier: hybridPolicy.feedback_boost.max_multiplier }
                : {}),
            },
          }
        : {}),
      ...(hybridPolicy.topology
        ? {
            topology: {
              enabled: hybridPolicy.topology.enabled !== false,
              ...(hybridPolicy.topology.mode === 'walk' ? { mode: 'walk' as const } : {}),
              ...(typeof hybridPolicy.topology.seed_k === 'number'
                ? { seedK: hybridPolicy.topology.seed_k }
                : {}),
              ...(typeof hybridPolicy.topology.max_hops === 'number'
                ? { maxHops: hybridPolicy.topology.max_hops }
                : {}),
              ...(typeof hybridPolicy.topology.hop_decay === 'number'
                ? { hopDecay: hybridPolicy.topology.hop_decay }
                : {}),
              ...(typeof hybridPolicy.topology.include_paths === 'boolean'
                ? { includePaths: hybridPolicy.topology.include_paths }
                : {}),
              ...(hybridPolicy.topology.edge_policy
                ? {
                    edgePolicy: Object.fromEntries(
                      Object.entries(
                        hybridPolicy.topology.edge_policy as Record<string, TopologyEdgePolicyEntry>
                      ).map(([key, value]) => [
                        key,
                        {
                          ...(typeof value.weight === 'number' ? { weight: value.weight } : {}),
                          ...(value.direction === 'forward' || value.direction === 'both'
                            ? { direction: value.direction }
                            : {}),
                          ...(value.action === 'boost' ||
                          value.action === 'flag_conflict' ||
                          value.action === 'shadow_old'
                            ? { action: value.action }
                            : {}),
                        },
                      ])
                    ),
                  }
                : {}),
            },
          }
        : {}),
    };
    const topologyConfig = resolveTopologyConfig(searchConfig.topology);
    const connectivityFilterSet = {
      scopes: scope as string[],
      boundaryClasses: allowedBoundaryClasses,
      ...(resolvedKindFilter ? { kindFilter: resolvedKindFilter } : {}),
      ...(resolvedMemoryTypeFilter ? { memoryTypeFilter: resolvedMemoryTypeFilter } : {}),
      excludedWorkingStateStatuses: getActivateExcludedWorkingStateStatuses(includeStaleTasks),
      ...(topologyConfig ? { topology: topologyConfig } : {}),
    };
    const directCandidateLimit =
      cursor !== undefined
        ? Number.MAX_SAFE_INTEGER
        : Math.max(
            resolvedTopK + 1,
            resolvedTopK * CONNECTIVITY_SEED_MULTIPLIER,
            (topologyConfig?.seedK ?? 0) * CONNECTIVITY_SEED_MULTIPLIER
          );
    const disableGraphPresenceInjection = debug_disable_graph_presence_injection === true;

    let searchResults: ActivateSearchItem[];
    let nextCursor: string | undefined;
    let hasMore: boolean;

    if (includeObservations) {
      const [durableResults, observationResults] = await Promise.all([
        hybridSearchWithScores(scope, directCandidateLimit, q, searchConfig),
        searchObservationsWithScores(q, {
          boundaryClasses: allowedBoundaryClasses,
          limit: directCandidateLimit,
        }),
      ]);
      const expandedDurableResults = await expandActivateResultsWithClaimLinks(
        durableResults.map((item) => ({ ...item, source: 'search' as const })),
        connectivityFilterSet
      );
      const normalizedObservationResults = normalizeObservationScoresForActivate(
        expandedDurableResults,
        observationResults.map((item) => ({ ...item, source: 'observation' as const }))
      );
      const pagedResults = pageActivateResultsWithObservationCap({
        durableResults: expandedDurableResults,
        observationResults: normalizedObservationResults,
        topK: resolvedTopK,
        ...(disableGraphPresenceInjection ? { disableGraphPresenceInjection: true } : {}),
        ...(cursor !== undefined ? { cursor } : {}),
      });

      searchResults = pagedResults.searchResults;
      nextCursor = pagedResults.nextCursor;
      hasMore = pagedResults.hasMore;
    } else {
      const durableResults = await hybridSearchWithScores(
        scope,
        directCandidateLimit,
        q,
        searchConfig
      );
      const expandedDurableResults = await expandActivateResultsWithClaimLinks(
        durableResults.map((item) => ({ ...item, source: 'search' as const })),
        connectivityFilterSet
      );
      const pagedResults = pageActivateResults({
        results: expandedDurableResults,
        topK: resolvedTopK,
        ...(disableGraphPresenceInjection ? { disableGraphPresenceInjection: true } : {}),
        ...(cursor !== undefined ? { cursor } : {}),
      });
      searchResults = pagedResults.searchResults;
      nextCursor = pagedResults.nextCursor;
      hasMore = pagedResults.hasMore;
    }

    const freshnessMatches = await findNewerSimilarClaims(
      searchResults.map((result) => result.claim.id)
    ).catch(() => new Map());
    const freshnessByClaimId = new Map<string, FreshnessMetadata>(
      [...freshnessMatches.entries()].map(([claimId, freshness]) => [
        claimId,
        {
          freshness: freshness.freshness,
          newer_similar: freshness.newer_similar,
        },
      ])
    );
    if (freshnessByClaimId.size > 0) {
      searchResults = [...searchResults].sort((left, right) =>
        compareActivateSearchItemsWithFreshness(left, right, freshnessByClaimId)
      );
    }

    const retrievedAt = new Date().toISOString();
    const claims = searchResults.map((r) => {
      if ((r.claim as { source_record_type?: string }).source_record_type === 'observation') {
        return r.claim;
      }

      return {
        ...r.claim,
        retrieval_count: r.claim.retrieval_count + 1,
        last_retrieved_at: retrievedAt,
      };
    });
    const durableClaimIds = searchResults
      .map((item) => item.claim)
      .filter(
        (claim): claim is Claim =>
          (claim as { source_record_type?: string }).source_record_type !== 'observation'
      )
      .map((claim) => claim.id);
    await recordClaimRetrievals(durableClaimIds, retrievedAt);
    const acId = `ac_${crypto.randomUUID().slice(0, 8)}`;
    await saveActiveContext({
      id: acId,
      claims,
      ...(resolvedIntent ? { intent: resolvedIntent } : {}),
      policy_version: getPolicyVersion(),
    });

    let evidenceMap: Map<string, Evidence[]> | undefined;
    if (include_meta && claims.length > 0) {
      const claimIds = claims.map((c) => c.id);
      evidenceMap = await getEvidenceForClaims(claimIds);
    }

    const scoredItems = searchResults.map((r, index) => {
      const updatedClaim =
        (r.claim as { source_record_type?: string }).source_record_type === 'observation'
          ? r.claim
          : {
              ...r.claim,
              retrieval_count: (r.claim.retrieval_count ?? 0) + 1,
              last_retrieved_at: retrievedAt,
            };
      const claim = augmentClaimWithFreshness(updatedClaim, freshnessByClaimId);
      const sourceLayer = r.source_layer ?? mapScopeToLayer(r.claim.scope);
      const rank = index + 1;
      const selectionReason = buildSelectionReason({
        score: r.score,
        claim,
        source_layer: sourceLayer,
        rank,
        ...(r.source ? { source: r.source } : {}),
        ...(r.link
          ? {
              link: {
                via_claim_id: r.link.via_claim_id,
                link_type: r.link.link_type,
                confidence: r.link.confidence,
              },
            }
          : {}),
        ...(r.topology ? { topology: r.topology } : {}),
        ...(r.score_breakdown ? { score_breakdown: r.score_breakdown } : {}),
        ...(resolvedIntent ? { intent: resolvedIntent } : {}),
      });

      return {
        claim,
        score: r.score,
        source_layer: sourceLayer,
        ...(r.source ? { source: r.source } : {}),
        ...(r.link ? { link: r.link } : {}),
        ...(r.topology ? { topology: r.topology } : {}),
        rank,
        ...(r.score_breakdown ? { score_breakdown: r.score_breakdown } : {}),
        selection_reason: selectionReason,
        evidences: evidenceMap?.get(claim.id) ?? [],
      };
    });

    await saveActiveContextItems(
      scoredItems.map((item) => ({
        id: `aci_${crypto.randomUUID().slice(0, 8)}`,
        active_context_id: acId,
        claim_id: item.claim.id,
        source_layer: item.source_layer,
        score: item.score,
        ...(item.score_breakdown ? { score_breakdown: item.score_breakdown } : {}),
        ...(item.topology
          ? { topology_metadata: item.topology as unknown as Record<string, unknown> }
          : {}),
        selection_reason: item.selection_reason,
        rank: item.rank,
      }))
    );

    let maintenanceHints: Awaited<ReturnType<typeof collectMaintenanceHints>> | undefined =
      undefined;
    if (maintenancePolicy.hints_enabled !== false) {
      try {
        maintenanceHints = await collectMaintenanceHints(
          claims.map((claim) => {
            const hintClaim = claim as Claim & {
              source_record_type?: string;
              transient?: boolean;
            };

            return {
              id: hintClaim.id,
              text: hintClaim.text,
              ...(typeof hintClaim.source_record_type === 'string'
                ? { source_record_type: hintClaim.source_record_type }
                : {}),
              ...(typeof hintClaim.transient === 'boolean'
                ? { transient: hintClaim.transient }
                : {}),
            };
          }),
          {
            similarityThreshold: maintenancePolicy.similarity_threshold ?? 0.9,
            staleDays: maintenancePolicy.stale_days ?? 30,
          }
        );
      } catch {
        // Maintenance hints are best-effort and must not fail activate.
        maintenanceHints = undefined;
      }
    }

    transitionToReady(acId);

    await appendLog({
      id: `log_${reqId}`,
      op: 'activate',
      ok: true,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    // safeJsonStringifyを使用してBigInt値を安全にシリアライズ
    return createToolResult(
      {
        active_context_id: acId,
        ...(resolvedIntent ? { intent: resolvedIntent } : {}),
        claims: scoredItems,
        claims_count: claims.length,
        next_cursor: nextCursor,
        has_more: hasMore,
        ...(maintenanceHints ? { maintenance_hints: maintenanceHints } : {}),
        policy_version: getPolicyVersion(),
        state: getStateType(),
        request_id: reqId,
        trace_id: traceId,
      },
      { useSafeStringify: true }
    );
  } catch (e: unknown) {
    await appendLog({
      id: `log_${reqId}`,
      op: 'activate',
      ok: false,
      req: reqId,
      trace: traceId,
      policy_version: getPolicyVersion(),
    });
    const msg = e instanceof Error ? e.message : String(e);
    return createToolResult(
      { ...err('ACTIVATE_FAILED', msg, reqId), trace_id: traceId },
      { isError: true }
    );
  }
}

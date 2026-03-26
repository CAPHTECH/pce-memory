import { getConnection } from '../db/connection.js';
import { findClaimsByIds } from './claims.js';
import type { Claim } from './claims.js';
import type { ClaimLinkType } from './claimLinks.js';
import type { ClaimKind, ClaimStatus, MemoryType } from '../domain/types.js';
import type {
  ResolvedTopologyConfig,
  TopologyEdgeAction,
  TopologyEdgeDirection,
} from './search/types.js';
import type { TopologyPathSegmentBreakdown, TopologyScoreBreakdown } from './rerank.js';

export interface TopologySeed {
  claim: Claim;
  score: number;
}

export interface TopologyFilters {
  scopes: string[];
  boundaryClasses: string[];
  kindFilter?: ClaimKind[];
  memoryTypeFilter?: MemoryType[];
  excludedWorkingStateStatuses: ClaimStatus[];
}

export interface TopologyDerivedItem {
  claim: Claim;
  score: number;
  source: 'claim_link' | 'topology';
  link?: {
    id: string;
    via_claim_id: string;
    link_type: ClaimLinkType;
    confidence: number;
  };
  topology: TopologyScoreBreakdown;
}

export interface TopologyWalkResult {
  derivedItems: TopologyDerivedItem[];
  shadowedClaimIds: string[];
  seedConflicts: Map<string, NonNullable<TopologyScoreBreakdown['conflicts']>>;
}

interface ClaimLinkEdgeRow {
  id: string;
  source_claim_id: string;
  target_claim_id: string;
  link_type: ClaimLinkType;
  confidence: number;
}

interface EntityPathEdgeRow {
  from_claim_id: string;
  to_claim_id: string;
  seed_entity_id: string;
  related_entity_id: string;
  relation_id: string;
  relation_type: string;
  relation_direction: 'forward' | 'reverse';
}

interface FrontierState {
  currentClaimId: string;
  seedClaimId: string;
  seedScore: number;
  depth: number;
  edgeProduct: number;
  visitedClaimIds: Set<string>;
  path: TopologyPathSegmentBreakdown[];
}

interface CandidateProposal {
  claimId: string;
  source: 'claim_link' | 'topology';
  kind: TopologyScoreBreakdown['kind'];
  link?: {
    id: string;
    via_claim_id: string;
    link_type: ClaimLinkType;
    confidence: number;
  };
  topology: TopologyScoreBreakdown;
  shadowedClaimIds?: string[];
  conflict?: {
    claim_id: string;
    link_type: ClaimLinkType;
    via_claim_id: string;
  };
  nextState?: FrontierState;
}

function claimMatchesFilters(claim: Claim, input: TopologyFilters): boolean {
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

async function fetchClaimLinkEdges(frontierClaimIds: readonly string[]): Promise<ClaimLinkEdgeRow[]> {
  if (frontierClaimIds.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const placeholders = frontierClaimIds.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT id, source_claim_id, target_claim_id, link_type, confidence
     FROM claim_links
     WHERE source_claim_id IN (${placeholders})
        OR target_claim_id IN (${placeholders})`,
    [...frontierClaimIds]
  );
  return reader.getRowObjects() as unknown as ClaimLinkEdgeRow[];
}

async function fetchEntityPathEdges(frontierClaimIds: readonly string[]): Promise<EntityPathEdgeRow[]> {
  if (frontierClaimIds.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const placeholders = frontierClaimIds.map((_, index) => `$${index + 1}`).join(',');
  const reader = await conn.runAndReadAll(
    `SELECT DISTINCT
       seed.claim_id AS from_claim_id,
       sibling.claim_id AS to_claim_id,
       seed.entity_id AS seed_entity_id,
       sibling.entity_id AS related_entity_id,
       r.id AS relation_id,
       r.type AS relation_type,
       CASE WHEN r.src_id = seed.entity_id THEN 'forward' ELSE 'reverse' END AS relation_direction
     FROM claim_entities seed
     INNER JOIN relations r
       ON r.src_id = seed.entity_id
       OR r.dst_id = seed.entity_id
     INNER JOIN claim_entities sibling
       ON sibling.entity_id = CASE
         WHEN r.src_id = seed.entity_id THEN r.dst_id
         ELSE r.src_id
       END
     WHERE seed.claim_id IN (${placeholders})
       AND sibling.claim_id <> seed.claim_id`,
    [...frontierClaimIds]
  );
  return reader.getRowObjects() as unknown as EntityPathEdgeRow[];
}

function createTopologyBreakdown(input: {
  seedClaimId: string;
  kind: TopologyScoreBreakdown['kind'];
  depth: number;
  hopDecay: number;
  edgeProduct: number;
  seedScore: number;
  path: TopologyPathSegmentBreakdown[];
  includePaths: boolean;
  shadowedClaimIds?: string[];
}): TopologyScoreBreakdown {
  const multiplier = input.edgeProduct * Math.pow(input.hopDecay, input.depth);
  return {
    seed_claim_id: input.seedClaimId,
    kind: input.kind,
    depth: input.depth,
    hop_decay: input.hopDecay,
    multiplier: Number(multiplier.toFixed(6)),
    path_score: Number((input.seedScore * multiplier).toFixed(6)),
    ...(input.shadowedClaimIds && input.shadowedClaimIds.length > 0
      ? { shadowed_claim_ids: input.shadowedClaimIds }
      : {}),
    ...(input.includePaths ? { path: input.path } : {}),
  };
}

function resolveClaimLinkNeighbor(input: {
  state: FrontierState;
  edge: ClaimLinkEdgeRow;
  direction: TopologyEdgeDirection;
  action: TopologyEdgeAction;
}): { neighborId?: string; shadowedClaimIds?: string[] } {
  const { state, edge, direction, action } = input;

  if (action === 'shadow_old') {
    if (state.currentClaimId === edge.target_claim_id) {
      return {
        neighborId: edge.source_claim_id,
        shadowedClaimIds: [edge.target_claim_id],
      };
    }
    if (state.currentClaimId === edge.source_claim_id) {
      return {
        shadowedClaimIds: [edge.target_claim_id],
      };
    }
    return {};
  }

  if (direction === 'forward') {
    if (state.currentClaimId === edge.source_claim_id) {
      return { neighborId: edge.target_claim_id };
    }
    return {};
  }

  if (state.currentClaimId === edge.source_claim_id) {
    return { neighborId: edge.target_claim_id };
  }
  if (state.currentClaimId === edge.target_claim_id) {
    return { neighborId: edge.source_claim_id };
  }
  return {};
}

function classifyClaimLinkSource(path: readonly TopologyPathSegmentBreakdown[]): 'claim_link' | 'topology' {
  return path.length === 1 && path[0]?.kind === 'claim_link' ? 'claim_link' : 'topology';
}

export async function walkTopologyFromSeeds(
  seeds: readonly TopologySeed[],
  filters: TopologyFilters,
  config: ResolvedTopologyConfig
): Promise<TopologyWalkResult> {
  if (!config.enabled || seeds.length === 0) {
    return {
      derivedItems: [],
      shadowedClaimIds: [],
      seedConflicts: new Map(),
    };
  }

  const frontier: FrontierState[] = seeds.slice(0, config.seedK).map((seed) => ({
    currentClaimId: seed.claim.id,
    seedClaimId: seed.claim.id,
    seedScore: seed.score,
    depth: 0,
    edgeProduct: 1,
    visitedClaimIds: new Set([seed.claim.id]),
    path: [],
  }));
  const derivedByClaimId = new Map<string, TopologyDerivedItem>();
  const shadowedClaimIds = new Set<string>();
  const seedConflicts = new Map<string, NonNullable<TopologyScoreBreakdown['conflicts']>>();

  let currentFrontier = frontier;
  for (let hop = 1; hop <= config.maxHops && currentFrontier.length > 0; hop++) {
    const frontierIds = [...new Set(currentFrontier.map((state) => state.currentClaimId))];
    const [claimLinkEdges, entityPathEdges] = await Promise.all([
      fetchClaimLinkEdges(frontierIds),
      fetchEntityPathEdges(frontierIds),
    ]);

    const proposals: CandidateProposal[] = [];
    for (const state of currentFrontier) {
      for (const edge of claimLinkEdges) {
        if (edge.source_claim_id !== state.currentClaimId && edge.target_claim_id !== state.currentClaimId) {
          continue;
        }

        const policy = config.edgePolicy[edge.link_type];
        const neighbor = resolveClaimLinkNeighbor({
          state,
          edge,
          direction: policy.direction,
          action: policy.action,
        });
        if (!neighbor.neighborId || state.visitedClaimIds.has(neighbor.neighborId)) {
          continue;
        }

        const nextPath = [
          ...state.path,
          {
            kind: 'claim_link' as const,
            from_claim_id: state.currentClaimId,
            to_claim_id: neighbor.neighborId,
            weight: policy.weight,
            confidence: Number(edge.confidence),
            link_id: edge.id,
            link_type: edge.link_type,
          },
        ];
        const edgeProduct = state.edgeProduct * policy.weight * Number(edge.confidence);
        const topology = createTopologyBreakdown({
          seedClaimId: state.seedClaimId,
          kind:
            policy.action === 'flag_conflict'
              ? 'conflict'
              : policy.action === 'shadow_old'
                ? 'supersession'
                : 'support',
          depth: hop,
          hopDecay: config.hopDecay,
          edgeProduct,
          seedScore: state.seedScore,
          path: nextPath,
          includePaths: config.includePaths,
          ...(neighbor.shadowedClaimIds ? { shadowedClaimIds: neighbor.shadowedClaimIds } : {}),
        });

        proposals.push({
          claimId: neighbor.neighborId,
          source: classifyClaimLinkSource(nextPath),
          kind: topology.kind,
          link: {
            id: edge.id,
            via_claim_id: state.currentClaimId,
            link_type: edge.link_type,
            confidence: Number(Number(edge.confidence).toFixed(4)),
          },
          topology,
          ...(neighbor.shadowedClaimIds ? { shadowedClaimIds: neighbor.shadowedClaimIds } : {}),
          ...(policy.action === 'flag_conflict'
            ? {
                conflict: {
                  claim_id: neighbor.neighborId,
                  link_type: edge.link_type,
                  via_claim_id: state.currentClaimId,
                },
              }
            : {}),
          ...(policy.action !== 'flag_conflict'
            ? {
                nextState: {
                  currentClaimId: neighbor.neighborId,
                  seedClaimId: state.seedClaimId,
                  seedScore: state.seedScore,
                  depth: hop,
                  edgeProduct,
                  visitedClaimIds: new Set([...state.visitedClaimIds, neighbor.neighborId]),
                  path: nextPath,
                },
              }
            : {}),
        });
      }

      for (const edge of entityPathEdges) {
        if (edge.from_claim_id !== state.currentClaimId || state.visitedClaimIds.has(edge.to_claim_id)) {
          continue;
        }

        const nextPath = [
          ...state.path,
          {
            kind: 'entity_relation' as const,
            from_claim_id: state.currentClaimId,
            to_claim_id: edge.to_claim_id,
            weight: config.entityPathWeight,
            confidence: config.entityPathConfidence,
            relation_id: edge.relation_id,
            relation_type: edge.relation_type,
            relation_direction: edge.relation_direction,
            via_entity_ids: [edge.seed_entity_id, edge.related_entity_id],
          },
        ];
        const edgeProduct = state.edgeProduct * config.entityPathWeight * config.entityPathConfidence;
        proposals.push({
          claimId: edge.to_claim_id,
          source: 'topology',
          kind: 'support',
          topology: createTopologyBreakdown({
            seedClaimId: state.seedClaimId,
            kind: 'support',
            depth: hop,
            hopDecay: config.hopDecay,
            edgeProduct,
            seedScore: state.seedScore,
            path: nextPath,
            includePaths: config.includePaths,
          }),
          nextState: {
            currentClaimId: edge.to_claim_id,
            seedClaimId: state.seedClaimId,
            seedScore: state.seedScore,
            depth: hop,
            edgeProduct,
            visitedClaimIds: new Set([...state.visitedClaimIds, edge.to_claim_id]),
            path: nextPath,
          },
        });
      }
    }

    const claimsById = new Map(
      (await findClaimsByIds([...new Set(proposals.map((proposal) => proposal.claimId))])).map((claim) => [
        claim.id,
        claim,
      ])
    );
    const nextFrontierByClaimId = new Map<string, FrontierState>();

    for (const proposal of proposals) {
      const claim = claimsById.get(proposal.claimId);
      if (!claim || !claimMatchesFilters(claim, filters)) {
        continue;
      }

      if (proposal.shadowedClaimIds) {
        for (const shadowedClaimId of proposal.shadowedClaimIds) {
          shadowedClaimIds.add(shadowedClaimId);
        }
      }
      if (proposal.conflict) {
        const conflicts = seedConflicts.get(proposal.topology.seed_claim_id) ?? [];
        conflicts.push(proposal.conflict);
        seedConflicts.set(proposal.topology.seed_claim_id, conflicts);
      }

      const existing = derivedByClaimId.get(claim.id);
      if (!existing || proposal.topology.path_score > existing.score) {
        derivedByClaimId.set(claim.id, {
          claim,
          score: proposal.topology.path_score,
          source: proposal.source,
          ...(proposal.link ? { link: proposal.link } : {}),
          topology: proposal.topology,
        });
      }

      if (proposal.nextState) {
        const existingState = nextFrontierByClaimId.get(proposal.nextState.currentClaimId);
        const nextScore = proposal.topology.path_score;
        const existingScore = existingState
          ? existingState.seedScore *
            existingState.edgeProduct *
            Math.pow(config.hopDecay, existingState.depth)
          : Number.NEGATIVE_INFINITY;
        if (!existingState || nextScore > existingScore) {
          nextFrontierByClaimId.set(proposal.nextState.currentClaimId, proposal.nextState);
        }
      }
    }

    currentFrontier = [...nextFrontierByClaimId.values()];
  }

  return {
    derivedItems: [...derivedByClaimId.values()],
    shadowedClaimIds: [...shadowedClaimIds],
    seedConflicts,
  };
}

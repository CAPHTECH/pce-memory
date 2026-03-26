import { getConnection } from '../db/connection.js';
import type { Claim, Provenance } from './claims.js';
import type { Entity } from './entities.js';
import type { ClaimLinkType } from './claimLinks.js';
import type { ClaimStatus } from '../domain/types.js';

export type RollbackTopologyNeighborhoodKind = 'support' | 'conflict' | 'supersession';

export interface RollbackTopologyPathSegment {
  kind: 'claim_link' | 'entity_relation';
  from_claim_id: string;
  to_claim_id: string;
  weight: number;
  confidence: number;
  link_id?: string;
  link_type?: ClaimLinkType;
  relation_id?: string;
  relation_type?: string;
  relation_direction?: 'forward' | 'reverse';
  via_entity_ids?: string[];
}

export interface RollbackTopologyProposal {
  claim_id: string;
  kind: RollbackTopologyNeighborhoodKind;
  score: number;
  depth: number;
  source: 'claim_links' | 'entity_graph';
  path: RollbackTopologyPathSegment[];
}

export interface RollbackTopologyNeighborhoodItem {
  claim: Claim;
  kind: RollbackTopologyNeighborhoodKind;
  score: number;
  depth: number;
  source: 'claim_links' | 'entity_graph';
  path: RollbackTopologyPathSegment[];
}

export interface RollbackTopologyConnectedClaim {
  claim: Claim;
  kinds: RollbackTopologyNeighborhoodKind[];
  score: number;
  depth: number;
  source: 'claim_links' | 'entity_graph';
  path: RollbackTopologyPathSegment[];
}

export interface RollbackTopologyLinkedEntity {
  entity: Entity;
  claim_ids: string[];
  score: number;
}

export interface RollbackTopologyActiveContext {
  active_context_id: string;
  claim_ids: string[];
  item_count: number;
  source_layers: string[];
  max_score: number;
}

export interface RollbackTopologyBlastRadius {
  root_claim: Claim;
  scope: string;
  target_layer: string;
  connected_claims: RollbackTopologyConnectedClaim[];
  linked_entities: RollbackTopologyLinkedEntity[];
  affected_active_contexts: RollbackTopologyActiveContext[];
  neighborhoods: {
    support: RollbackTopologyNeighborhoodItem[];
    conflict: RollbackTopologyNeighborhoodItem[];
    supersession: RollbackTopologyNeighborhoodItem[];
  };
  summary: {
    connected_claims: number;
    linked_entities: number;
    affected_active_contexts: number;
    support: number;
    conflict: number;
    supersession: number;
  };
}

export interface RollbackTopologyOptions {
  maxHops?: number;
  hopDecay?: number;
  entityPathWeight?: number;
  entityPathConfidence?: number;
  includePaths?: boolean;
}

interface ClaimLinkEdgeRow {
  id: string;
  source_claim_id: string;
  target_claim_id: string;
  link_type: ClaimLinkType;
  confidence: number | string | null;
}

interface ClaimEntityRow {
  claim_id: string;
  entity_id: string;
}

interface EntityClaimRow {
  claim_id: string;
  entity_id: string;
}

interface EntityRelationRow {
  id: string;
  src_id: string;
  dst_id: string;
  type: string;
  evidence_claim_id: string | null;
}

interface ClaimRow {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  memory_type: string | null;
  status: ClaimStatus | string | null;
  content_hash: string;
  utility: number | string;
  confidence: number | string;
  created_at: string | Date;
  updated_at: string | Date;
  recency_anchor: string | Date;
  retrieval_count: number | string;
  last_retrieved_at: string | Date | null;
  provenance: Provenance | string | null;
  tombstone: boolean | number | null;
  tombstone_at: string | Date | null;
  rollback_reason: string | null;
  superseded_by: string | null;
}

interface EntityRow {
  id: string;
  type: Entity['type'];
  name: string;
  canonical_key: string | null;
  attrs: Entity['attrs'] | string | null;
  claim_id: string;
}

interface ActiveContextItemRow {
  active_context_id: string;
  claim_id: string;
  source_layer: string | null;
  score: number | string | null;
}

const DEFAULT_MAX_HOPS = 2;
const DEFAULT_HOP_DECAY = 0.75;
const DEFAULT_ENTITY_PATH_WEIGHT = 0.45;
const DEFAULT_ENTITY_PATH_CONFIDENCE = 1.0;

const CLAIM_LINK_WEIGHTS: Record<ClaimLinkType, number> = {
  supports: 0.9,
  extends: 0.7,
  related: 0.35,
  contradicts: 0.15,
  supersedes: 1.0,
};

const KIND_BY_LINK_TYPE: Record<ClaimLinkType, RollbackTopologyNeighborhoodKind> = {
  supports: 'support',
  extends: 'support',
  related: 'support',
  contradicts: 'conflict',
  supersedes: 'supersession',
};

function mapScopeToLayer(scope: string): string {
  if (scope === 'principle') return 'macro';
  if (scope === 'project') return 'meso';
  return 'micro';
}

function normalizeConfidence(value: number | string | null | undefined): number {
  const numeric = Number(value);
  if (!Number.isFinite(numeric)) {
    return 1;
  }
  return Math.max(0, Math.min(1, numeric));
}

function normalizeScore(value: number | string | null | undefined): number {
  const numeric = Number(value);
  return Number.isFinite(numeric) ? numeric : 0;
}

function buildInClause(
  values: readonly string[],
  startIndex: number = 1
): { clause: string; params: string[] } {
  const params = [...values];
  const clause = params.map((_, index) => `$${startIndex + index}`).join(',');
  return { clause, params };
}

function parseEntityRow(row: EntityRow): Entity {
  let attrs: Entity['attrs'];
  if (typeof row.attrs === 'string') {
    try {
      attrs = JSON.parse(row.attrs) as Record<string, unknown>;
    } catch {
      attrs = undefined;
    }
  } else if (row.attrs && typeof row.attrs === 'object') {
    attrs = row.attrs as Record<string, unknown>;
  } else {
    attrs = undefined;
  }

  const entity: Entity = {
    id: row.id,
    type: row.type,
    name: row.name,
  };
  if (row.canonical_key !== null && row.canonical_key !== undefined) {
    entity.canonical_key = row.canonical_key;
  }
  if (attrs !== undefined) {
    entity.attrs = attrs;
  }
  return entity;
}

function parseClaimRow(row: ClaimRow): Claim {
  let provenance: Provenance | undefined;
  if (typeof row.provenance === 'string') {
    try {
      provenance = JSON.parse(row.provenance) as Provenance;
    } catch {
      provenance = undefined;
    }
  } else if (row.provenance && typeof row.provenance === 'object') {
    provenance = row.provenance;
  }

  const claim: Claim = {
    id: row.id,
    text: row.text,
    kind: row.kind,
    scope: row.scope,
    boundary_class: row.boundary_class,
    memory_type:
      row.memory_type === null || row.memory_type === undefined
        ? null
        : (row.memory_type as NonNullable<Claim['memory_type']>),
    status: (row.status ?? 'active') as ClaimStatus,
    content_hash: row.content_hash,
    utility: normalizeScore(row.utility),
    confidence: normalizeScore(row.confidence),
    created_at: row.created_at instanceof Date ? row.created_at.toISOString() : row.created_at,
    updated_at: row.updated_at instanceof Date ? row.updated_at.toISOString() : row.updated_at,
    recency_anchor:
      row.recency_anchor instanceof Date ? row.recency_anchor.toISOString() : row.recency_anchor,
    retrieval_count: Math.max(0, Math.floor(normalizeScore(row.retrieval_count))),
    last_retrieved_at:
      row.last_retrieved_at instanceof Date
        ? row.last_retrieved_at.toISOString()
        : row.last_retrieved_at,
    tombstone: Boolean(row.tombstone),
    tombstone_at:
      row.tombstone_at instanceof Date ? row.tombstone_at.toISOString() : row.tombstone_at,
    rollback_reason: row.rollback_reason ?? null,
    superseded_by: row.superseded_by ?? null,
  };

  if (provenance) {
    claim.provenance = provenance;
  }

  return claim;
}

async function fetchRows<T>(sql: string, params: string[]): Promise<T[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(sql, params);
  return reader.getRowObjects() as unknown as T[];
}

async function fetchClaimById(claimId: string): Promise<Claim | undefined> {
  const rows = await fetchRows<ClaimRow>(
    `SELECT id, text, kind, scope, boundary_class, memory_type, status, content_hash,
            utility, confidence, created_at, updated_at, recency_anchor, retrieval_count,
            last_retrieved_at, provenance, tombstone, tombstone_at, rollback_reason, superseded_by
     FROM claims
     WHERE id = $1
     LIMIT 1`,
    [claimId]
  );
  return rows[0] ? parseClaimRow(rows[0]) : undefined;
}

async function fetchClaimsByIds(claimIds: readonly string[]): Promise<Claim[]> {
  if (claimIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(claimIds);
  const rows = await fetchRows<ClaimRow>(
    `SELECT id, text, kind, scope, boundary_class, memory_type, status, content_hash,
            utility, confidence, created_at, updated_at, recency_anchor, retrieval_count,
            last_retrieved_at, provenance, tombstone, tombstone_at, rollback_reason, superseded_by
     FROM claims
     WHERE id IN (${clause})`,
    params
  );
  const claimsById = new Map(rows.map((row) => [row.id, parseClaimRow(row)]));
  return claimIds
    .map((claimId) => claimsById.get(claimId))
    .filter((claim): claim is Claim => claim !== undefined);
}

async function fetchClaimLinks(claimIds: readonly string[]): Promise<ClaimLinkEdgeRow[]> {
  if (claimIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(claimIds);
  return fetchRows<ClaimLinkEdgeRow>(
    `SELECT id, source_claim_id, target_claim_id, link_type, confidence
     FROM claim_links
     WHERE source_claim_id IN (${clause})
        OR target_claim_id IN (${clause})`,
    params
  );
}

async function fetchClaimEntities(claimIds: readonly string[]): Promise<ClaimEntityRow[]> {
  if (claimIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(claimIds);
  return fetchRows<ClaimEntityRow>(
    `SELECT claim_id, entity_id
     FROM claim_entities
     WHERE claim_id IN (${clause})`,
    params
  );
}

async function fetchClaimIdsByEntityIds(entityIds: readonly string[]): Promise<EntityClaimRow[]> {
  if (entityIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(entityIds);
  return fetchRows<EntityClaimRow>(
    `SELECT claim_id, entity_id
     FROM claim_entities
     WHERE entity_id IN (${clause})`,
    params
  );
}

async function fetchEntitiesByIds(
  entityIds: readonly string[],
  claimIds: readonly string[]
): Promise<EntityRow[]> {
  if (entityIds.length === 0 || claimIds.length === 0) {
    return [];
  }

  const { clause: entityClause, params: entityParams } = buildInClause(entityIds, 1);
  const { clause: claimClause, params: claimParams } = buildInClause(
    claimIds,
    entityParams.length + 1
  );
  return fetchRows<EntityRow>(
    `SELECT e.id, e.type, e.name, e.canonical_key, e.attrs, ce.claim_id
     FROM entities e
     INNER JOIN claim_entities ce ON ce.entity_id = e.id
     WHERE e.id IN (${entityClause})
       AND ce.claim_id IN (${claimClause})`,
    [...entityParams, ...claimParams]
  );
}

async function fetchEntityRelations(entityIds: readonly string[]): Promise<EntityRelationRow[]> {
  if (entityIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(entityIds);
  return fetchRows<EntityRelationRow>(
    `SELECT id, src_id, dst_id, type, evidence_claim_id
     FROM relations
     WHERE src_id IN (${clause})
        OR dst_id IN (${clause})`,
    params
  );
}

async function fetchActiveContextItems(
  claimIds: readonly string[]
): Promise<ActiveContextItemRow[]> {
  if (claimIds.length === 0) {
    return [];
  }

  const { clause, params } = buildInClause(claimIds);
  return fetchRows<ActiveContextItemRow>(
    `SELECT active_context_id, claim_id, source_layer, score
     FROM active_context_items
     WHERE claim_id IN (${clause})`,
    params
  );
}

function edgeWeightForLinkType(linkType: ClaimLinkType): number {
  return CLAIM_LINK_WEIGHTS[linkType];
}

function classifyLinkType(linkType: ClaimLinkType): RollbackTopologyNeighborhoodKind {
  return KIND_BY_LINK_TYPE[linkType];
}

function buildClaimLinkPathSegment(input: {
  fromClaimId: string;
  toClaimId: string;
  edge: ClaimLinkEdgeRow;
  weight: number;
}): RollbackTopologyPathSegment {
  return {
    kind: 'claim_link',
    from_claim_id: input.fromClaimId,
    to_claim_id: input.toClaimId,
    weight: input.weight,
    confidence: normalizeConfidence(input.edge.confidence),
    link_id: input.edge.id,
    link_type: input.edge.link_type,
  };
}

function buildEntityPathSegment(input: {
  fromClaimId: string;
  toClaimId: string;
  seedEntityId: string;
  relatedEntityId: string;
  relation: EntityRelationRow;
  weight: number;
  confidence: number;
  relationDirection: 'forward' | 'reverse';
}): RollbackTopologyPathSegment {
  return {
    kind: 'entity_relation',
    from_claim_id: input.fromClaimId,
    to_claim_id: input.toClaimId,
    weight: input.weight,
    confidence: input.confidence,
    relation_id: input.relation.id,
    relation_type: input.relation.type,
    relation_direction: input.relationDirection,
    via_entity_ids: [input.seedEntityId, input.relatedEntityId],
  };
}

type FrontierState = {
  claimId: string;
  score: number;
  depth: number;
  source: 'claim_links' | 'entity_graph';
  path: RollbackTopologyPathSegment[];
};

type KindRecord = Omit<RollbackTopologyNeighborhoodItem, 'claim'>;

interface ConnectedClaimRecord {
  claim: Claim;
  kinds: Set<RollbackTopologyNeighborhoodKind>;
  best: KindRecord;
  bestByKind: Partial<Record<RollbackTopologyNeighborhoodKind, KindRecord>>;
}

function upsertKindRecord(record: ConnectedClaimRecord, proposal: RollbackTopologyProposal): void {
  record.kinds.add(proposal.kind);
  const nextRecord: KindRecord = {
    kind: proposal.kind,
    score: proposal.score,
    depth: proposal.depth,
    source: proposal.source,
    path: proposal.path,
  };
  const currentForKind = record.bestByKind[proposal.kind];
  if (
    !currentForKind ||
    proposal.score > currentForKind.score ||
    (proposal.score === currentForKind.score && proposal.depth < currentForKind.depth)
  ) {
    record.bestByKind[proposal.kind] = nextRecord;
  }
  if (
    proposal.score > record.best.score ||
    (proposal.score === record.best.score && proposal.depth < record.best.depth)
  ) {
    record.best = nextRecord;
  }
}

function buildConnectedClaimRecord(
  claim: Claim,
  proposal: RollbackTopologyProposal
): ConnectedClaimRecord {
  return {
    claim,
    kinds: new Set([proposal.kind]),
    best: {
      kind: proposal.kind,
      score: proposal.score,
      depth: proposal.depth,
      source: proposal.source,
      path: proposal.path,
    },
    bestByKind: {
      [proposal.kind]: {
        kind: proposal.kind,
        score: proposal.score,
        depth: proposal.depth,
        source: proposal.source,
        path: proposal.path,
      },
    },
  };
}

function sortConnectedClaimRecords(
  left: ConnectedClaimRecord,
  right: ConnectedClaimRecord
): number {
  if (right.best.score !== left.best.score) {
    return right.best.score - left.best.score;
  }
  if (left.best.depth !== right.best.depth) {
    return left.best.depth - right.best.depth;
  }
  return left.claim.id.localeCompare(right.claim.id);
}

function sortNeighborhoodItems(
  left: RollbackTopologyNeighborhoodItem,
  right: RollbackTopologyNeighborhoodItem
): number {
  if (right.score !== left.score) {
    return right.score - left.score;
  }
  if (left.depth !== right.depth) {
    return left.depth - right.depth;
  }
  return left.claim.id.localeCompare(right.claim.id);
}

export async function collectRollbackTopologyBlastRadius(
  claimId: string,
  options: RollbackTopologyOptions = {}
): Promise<RollbackTopologyBlastRadius> {
  const rootClaim = await fetchClaimById(claimId);
  if (!rootClaim) {
    throw new Error(`claim not found: ${claimId}`);
  }

  const maxHops =
    typeof options.maxHops === 'number' && Number.isFinite(options.maxHops) && options.maxHops > 0
      ? Math.min(DEFAULT_MAX_HOPS, Math.floor(options.maxHops))
      : DEFAULT_MAX_HOPS;
  const hopDecay =
    typeof options.hopDecay === 'number' &&
    Number.isFinite(options.hopDecay) &&
    options.hopDecay > 0 &&
    options.hopDecay <= 1
      ? options.hopDecay
      : DEFAULT_HOP_DECAY;
  const entityPathWeight =
    typeof options.entityPathWeight === 'number' &&
    Number.isFinite(options.entityPathWeight) &&
    options.entityPathWeight >= 0
      ? options.entityPathWeight
      : DEFAULT_ENTITY_PATH_WEIGHT;
  const entityPathConfidence =
    typeof options.entityPathConfidence === 'number' &&
    Number.isFinite(options.entityPathConfidence) &&
    options.entityPathConfidence >= 0
      ? Math.min(1, options.entityPathConfidence)
      : DEFAULT_ENTITY_PATH_CONFIDENCE;

  const bestTraversalScoreByClaimId = new Map<string, number>([[rootClaim.id, 1]]);
  let frontier: FrontierState[] = [
    {
      claimId: rootClaim.id,
      score: 1,
      depth: 0,
      source: 'claim_links',
      path: [],
    },
  ];
  const connectedRecords = new Map<string, ConnectedClaimRecord>();
  for (let hop = 1; hop <= maxHops && frontier.length > 0; hop++) {
    const frontierClaimIds = [...new Set(frontier.map((state) => state.claimId))];
    const [claimLinkEdges, claimEntityRows] = await Promise.all([
      fetchClaimLinks(frontierClaimIds),
      fetchClaimEntities(frontierClaimIds),
    ]);

    const entitiesByClaimId = new Map<string, string[]>();
    for (const row of claimEntityRows) {
      const list = entitiesByClaimId.get(row.claim_id) ?? [];
      list.push(row.entity_id);
      entitiesByClaimId.set(row.claim_id, list);
    }

    const seedEntityIds = [...new Set(claimEntityRows.map((row) => row.entity_id))];
    const relations = await fetchEntityRelations(seedEntityIds);
    const relatedEntityIds = [
      ...new Set([
        ...seedEntityIds,
        ...relations.flatMap((relation) => [relation.src_id, relation.dst_id]),
      ]),
    ];
    const claimEntityMappings = await fetchClaimIdsByEntityIds(relatedEntityIds);

    const claimIdsByEntityId = new Map<string, string[]>();
    for (const row of claimEntityMappings) {
      const entityClaims = claimIdsByEntityId.get(row.entity_id) ?? [];
      entityClaims.push(row.claim_id);
      claimIdsByEntityId.set(row.entity_id, entityClaims);
    }

    const proposals: RollbackTopologyProposal[] = [];
    const traversalBestByClaimId = new Map<string, RollbackTopologyProposal>();

    for (const state of frontier) {
      for (const edge of claimLinkEdges) {
        if (edge.source_claim_id !== state.claimId && edge.target_claim_id !== state.claimId) {
          continue;
        }

        const nextClaimId =
          edge.source_claim_id === state.claimId ? edge.target_claim_id : edge.source_claim_id;
        if (nextClaimId === rootClaim.id) {
          continue;
        }

        const kind = classifyLinkType(edge.link_type);
        const nextScore =
          state.score *
          edgeWeightForLinkType(edge.link_type) *
          normalizeConfidence(edge.confidence) *
          hopDecay;
        const nextPath = [
          ...state.path,
          buildClaimLinkPathSegment({
            fromClaimId: state.claimId,
            toClaimId: nextClaimId,
            edge,
            weight: edgeWeightForLinkType(edge.link_type),
          }),
        ];
        const proposal: RollbackTopologyProposal = {
          claim_id: nextClaimId,
          kind,
          score: nextScore,
          depth: hop,
          source: 'claim_links',
          path: options.includePaths === false ? [] : nextPath,
        };
        proposals.push(proposal);
        const existingProposal = traversalBestByClaimId.get(nextClaimId);
        if (!existingProposal || proposal.score > existingProposal.score) {
          traversalBestByClaimId.set(nextClaimId, proposal);
        }
      }

      const frontierEntityIds = entitiesByClaimId.get(state.claimId) ?? [];
      if (frontierEntityIds.length === 0 || relations.length === 0) {
        continue;
      }

      for (const seedEntityId of frontierEntityIds) {
        for (const relation of relations) {
          if (relation.src_id !== seedEntityId && relation.dst_id !== seedEntityId) {
            continue;
          }

          const relatedEntityId =
            relation.src_id === seedEntityId ? relation.dst_id : relation.src_id;
          const relationDirection = relation.src_id === seedEntityId ? 'forward' : 'reverse';
          const claimIds = claimIdsByEntityId.get(relatedEntityId) ?? [];
          for (const nextClaimId of claimIds) {
            if (nextClaimId === state.claimId || nextClaimId === rootClaim.id) {
              continue;
            }
            const nextScore = state.score * entityPathWeight * entityPathConfidence * hopDecay;
            const nextPath = [
              ...state.path,
              buildEntityPathSegment({
                fromClaimId: state.claimId,
                toClaimId: nextClaimId,
                seedEntityId,
                relatedEntityId,
                relation,
                weight: entityPathWeight,
                confidence: entityPathConfidence,
                relationDirection,
              }),
            ];
            const proposal: RollbackTopologyProposal = {
              claim_id: nextClaimId,
              kind: 'support',
              score: nextScore,
              depth: hop,
              source: 'entity_graph',
              path: options.includePaths === false ? [] : nextPath,
            };
            proposals.push(proposal);
            const existingProposal = traversalBestByClaimId.get(nextClaimId);
            if (!existingProposal || proposal.score > existingProposal.score) {
              traversalBestByClaimId.set(nextClaimId, proposal);
            }
          }
        }
      }
    }

    const nextFrontierByClaimId = new Map<string, FrontierState>();
    const nextClaimIds = [...traversalBestByClaimId.keys()];
    const claims = await fetchClaimsByIds(nextClaimIds);
    const claimsById = new Map(claims.map((claim) => [claim.id, claim]));

    for (const proposal of proposals) {
      const claim = claimsById.get(proposal.claim_id);
      if (!claim) {
        continue;
      }

      const record = connectedRecords.get(claim.id);
      if (record) {
        upsertKindRecord(record, proposal);
      } else {
        connectedRecords.set(claim.id, buildConnectedClaimRecord(claim, proposal));
      }

      const currentBestTraversalScore = bestTraversalScoreByClaimId.get(claim.id) ?? 0;
      if (proposal.score > currentBestTraversalScore) {
        bestTraversalScoreByClaimId.set(claim.id, proposal.score);
        nextFrontierByClaimId.set(claim.id, {
          claimId: claim.id,
          score: proposal.score,
          depth: proposal.depth,
          source: proposal.source,
          path: proposal.path,
        });
      }
    }

    frontier = [...nextFrontierByClaimId.values()];
  }

  const connectedClaims = [...connectedRecords.values()].sort(sortConnectedClaimRecords);
  const connectedClaimIds = connectedClaims.map((item) => item.claim.id);
  const impactedClaimIds = [rootClaim.id, ...connectedClaimIds];

  const linkedEntityRows = await fetchEntitiesByIds(
    [...new Set((await fetchClaimEntities(impactedClaimIds)).map((row) => row.entity_id))],
    impactedClaimIds
  );
  const linkedEntitiesById = new Map<string, RollbackTopologyLinkedEntity>();
  for (const row of linkedEntityRows) {
    const entity = parseEntityRow(row);
    const existing = linkedEntitiesById.get(entity.id);
    const nextClaimIds = existing
      ? [...new Set([...existing.claim_ids, row.claim_id])]
      : [row.claim_id];
    const nextScore = existing ? Math.max(existing.score, 1) : 1;
    linkedEntitiesById.set(entity.id, {
      entity,
      claim_ids: nextClaimIds,
      score: nextScore,
    });
  }

  const activeContextRows = await fetchActiveContextItems(impactedClaimIds);
  const activeContextsById = new Map<string, RollbackTopologyActiveContext>();
  for (const row of activeContextRows) {
    const existing = activeContextsById.get(row.active_context_id);
    const nextClaimIds = existing
      ? [...new Set([...existing.claim_ids, row.claim_id])]
      : [row.claim_id];
    const nextSourceLayers = existing
      ? [...new Set([...existing.source_layers, row.source_layer ?? 'unknown'])]
      : [row.source_layer ?? 'unknown'];
    const nextMaxScore = existing
      ? Math.max(existing.max_score, normalizeScore(row.score))
      : normalizeScore(row.score);
    const nextItemCount = existing ? existing.item_count + 1 : 1;
    activeContextsById.set(row.active_context_id, {
      active_context_id: row.active_context_id,
      claim_ids: nextClaimIds,
      item_count: nextItemCount,
      source_layers: nextSourceLayers,
      max_score: nextMaxScore,
    });
  }

  const neighborhoods = {
    support: connectedClaims
      .filter((record) => record.kinds.has('support'))
      .map((record) => {
        const best = record.bestByKind.support ?? record.best;
        return {
          claim: record.claim,
          kind: 'support' as const,
          score: best.score,
          depth: best.depth,
          source: best.source,
          path: best.path,
        };
      })
      .sort(sortNeighborhoodItems),
    conflict: connectedClaims
      .filter((record) => record.kinds.has('conflict'))
      .map((record) => {
        const best = record.bestByKind.conflict ?? record.best;
        return {
          claim: record.claim,
          kind: 'conflict' as const,
          score: best.score,
          depth: best.depth,
          source: best.source,
          path: best.path,
        };
      })
      .sort(sortNeighborhoodItems),
    supersession: connectedClaims
      .filter((record) => record.kinds.has('supersession'))
      .map((record) => {
        const best = record.bestByKind.supersession ?? record.best;
        return {
          claim: record.claim,
          kind: 'supersession' as const,
          score: best.score,
          depth: best.depth,
          source: best.source,
          path: best.path,
        };
      })
      .sort(sortNeighborhoodItems),
  };

  return {
    root_claim: rootClaim,
    scope: rootClaim.scope,
    target_layer: mapScopeToLayer(rootClaim.scope),
    connected_claims: connectedClaims.map((record) => ({
      claim: record.claim,
      kinds: [...record.kinds],
      score: record.best.score,
      depth: record.best.depth,
      source: record.best.source,
      path: record.best.path,
    })),
    linked_entities: [...linkedEntitiesById.values()].sort((left, right) => {
      if (right.score !== left.score) {
        return right.score - left.score;
      }
      return left.entity.id.localeCompare(right.entity.id);
    }),
    affected_active_contexts: [...activeContextsById.values()].sort((left, right) =>
      left.active_context_id.localeCompare(right.active_context_id)
    ),
    neighborhoods,
    summary: {
      connected_claims: connectedClaims.length,
      linked_entities: linkedEntitiesById.size,
      affected_active_contexts: activeContextsById.size,
      support: neighborhoods.support.length,
      conflict: neighborhoods.conflict.length,
      supersession: neighborhoods.supersession.length,
    },
  };
}

import { getConnection } from '../db/connection.js';
import { listAllEntities } from './entities.js';
import { listAllRelations } from './relations.js';
import { listClaimsByFilter } from './claims.js';
import type { Claim } from './claims.js';

export type GraphAuditIssueKind =
  | 'orphan_claim'
  | 'orphan_entity'
  | 'contradiction_cycle'
  | 'supersession_chain'
  | 'scope_hole'
  | 'repeated_coactivation'
  | 'generic_hub';

export type GraphAuditSeverity = 'info' | 'warning' | 'critical';

export interface GraphAuditOptions {
  minSupersessionChainLength?: number;
  repeatedCoactivationThreshold?: number;
  genericHubDegreeThreshold?: number;
  maxFindingsPerKind?: number;
  scanLimit?: number;
}

export interface GraphAuditFinding {
  kind: GraphAuditIssueKind;
  severity: GraphAuditSeverity;
  message: string;
  node_ids?: string[];
  edge_ids?: string[];
  related_ids?: string[];
  context_ids?: string[];
  details?: Record<string, unknown>;
}

export interface GraphAuditComponent {
  id: string;
  claim_ids: string[];
  scope_counts: Record<string, number>;
  missing_scopes: string[];
}

export interface GraphAuditSummary {
  claims: number;
  entities: number;
  relations: number;
  claim_links: number;
  components: number;
  orphan_claims: number;
  orphan_entities: number;
  contradiction_cycles: number;
  supersession_chains: number;
  scope_holes: number;
  repeated_coactivations: number;
  generic_hubs: number;
  truncated?: boolean;
}

export interface GraphAuditTruncation {
  claims: boolean;
  entities: boolean;
  relations: boolean;
}

export interface GraphAuditReport {
  summary: GraphAuditSummary;
  truncation: GraphAuditTruncation;
  findings: GraphAuditFinding[];
  components: GraphAuditComponent[];
}

interface ClaimLinkRow {
  id: string;
  source_claim_id: string;
  target_claim_id: string;
  link_type: string;
}

interface ClaimEntityRow {
  claim_id: string;
  entity_id: string;
}

interface ActiveContextItemRow {
  active_context_id: string;
  claim_id: string;
}

interface EntityRow {
  id: string;
  name: string;
}

interface SupersessionPath {
  nodes: string[];
  edge_ids: string[];
}

const DEFAULT_MIN_SUPERSESSION_CHAIN_LENGTH = 3;
const DEFAULT_REPEATED_COACTIVATION_THRESHOLD = 3;
const DEFAULT_GENERIC_HUB_DEGREE_THRESHOLD = 4;
const DEFAULT_MAX_FINDINGS_PER_KIND = 20;
const DEFAULT_SCAN_LIMIT = 100_000;

const GENERIC_LABELS = new Set([
  'general',
  'overview',
  'summary',
  'notes',
  'note',
  'misc',
  'miscellaneous',
  'todo',
  'template',
  'sample',
  'example',
  'placeholder',
  'thing',
  'other',
  'default',
]);

function pairKey(left: string, right: string): string {
  return left < right ? `${left}::${right}` : `${right}::${left}`;
}

function sortedUnique(values: Iterable<string>): string[] {
  return [...new Set(values)].sort();
}

function ensureClaimAdjacency(map: Map<string, Set<string>>, claimId: string): Set<string> {
  const existing = map.get(claimId);
  if (existing) {
    return existing;
  }
  const next = new Set<string>();
  map.set(claimId, next);
  return next;
}

function addUndirectedClaimEdge(
  adjacency: Map<string, Set<string>>,
  directEvidence: Map<string, Set<string>>,
  left: string,
  right: string,
  reason: string
): void {
  if (left === right) {
    return;
  }
  ensureClaimAdjacency(adjacency, left).add(right);
  ensureClaimAdjacency(adjacency, right).add(left);
  const key = pairKey(left, right);
  const reasons = directEvidence.get(key) ?? new Set<string>();
  reasons.add(reason);
  directEvidence.set(key, reasons);
}

function addDirectedEdge(
  adjacency: Map<string, Array<{ to: string; edge_id: string }>>,
  from: string,
  to: string,
  edgeId: string
): void {
  const edges = adjacency.get(from) ?? [];
  edges.push({ to, edge_id: edgeId });
  adjacency.set(from, edges);
}

function isGenericLabel(value: string): boolean {
  const normalized = value.toLowerCase().replace(/[_-]+/g, ' ').trim();
  if (normalized.length === 0) {
    return true;
  }
  if (GENERIC_LABELS.has(normalized)) {
    return true;
  }

  const tokens = normalized.split(/\s+/).filter(Boolean);
  if (tokens.length <= 2 && normalized.length <= 24) {
    return true;
  }

  return tokens.some((token) => GENERIC_LABELS.has(token));
}

function canonicalizeCycle(nodes: string[]): string {
  if (nodes.length === 0) {
    return '';
  }

  const rotations: string[][] = [];
  for (let index = 0; index < nodes.length; index++) {
    rotations.push([...nodes.slice(index), ...nodes.slice(0, index)]);
  }

  return rotations.map((rotation) => rotation.join(' -> ')).sort()[0] as string;
}

function componentIdForIndex(index: number): string {
  return `component_${String(index + 1).padStart(3, '0')}`;
}

function limitFindingsPerKind(
  findings: GraphAuditFinding[],
  maxFindingsPerKind: number
): GraphAuditFinding[] {
  const counts = new Map<GraphAuditIssueKind, number>();
  const limited: GraphAuditFinding[] = [];

  for (const finding of findings) {
    const nextCount = (counts.get(finding.kind) ?? 0) + 1;
    if (nextCount > maxFindingsPerKind) {
      continue;
    }
    counts.set(finding.kind, nextCount);
    limited.push(finding);
  }

  return limited;
}

function chooseLongestPathFromRoot(
  root: string,
  adjacency: Map<string, Array<{ to: string; edge_id: string }>>,
  visiting: Set<string>,
  memo: Map<string, SupersessionPath | undefined>
): SupersessionPath | undefined {
  const cached = memo.get(root);
  if (cached !== undefined) {
    return cached;
  }

  if (visiting.has(root)) {
    return undefined;
  }

  visiting.add(root);
  const nextEdges = adjacency.get(root) ?? [];
  let best: SupersessionPath | undefined;

  for (const edge of nextEdges) {
    const childPath = chooseLongestPathFromRoot(edge.to, adjacency, visiting, memo);
    const candidate: SupersessionPath = childPath
      ? {
          nodes: [root, ...childPath.nodes],
          edge_ids: [edge.edge_id, ...childPath.edge_ids],
        }
      : {
          nodes: [root, edge.to],
          edge_ids: [edge.edge_id],
        };

    if (!best || candidate.edge_ids.length > best.edge_ids.length) {
      best = candidate;
    }
  }

  visiting.delete(root);
  memo.set(root, best);
  return best;
}

export async function auditGraph(options: GraphAuditOptions = {}): Promise<GraphAuditReport> {
  const minSupersessionChainLength =
    options.minSupersessionChainLength ?? DEFAULT_MIN_SUPERSESSION_CHAIN_LENGTH;
  const repeatedCoactivationThreshold =
    options.repeatedCoactivationThreshold ?? DEFAULT_REPEATED_COACTIVATION_THRESHOLD;
  const genericHubDegreeThreshold =
    options.genericHubDegreeThreshold ?? DEFAULT_GENERIC_HUB_DEGREE_THRESHOLD;
  const maxFindingsPerKind = options.maxFindingsPerKind ?? DEFAULT_MAX_FINDINGS_PER_KIND;
  const scanLimit =
    typeof options.scanLimit === 'number' &&
    Number.isFinite(options.scanLimit) &&
    options.scanLimit > 0
      ? Math.floor(options.scanLimit)
      : DEFAULT_SCAN_LIMIT;

  const [
    claimsLoaded,
    entitiesLoaded,
    relationsLoaded,
    claimLinks,
    claimEntities,
    activeContextItems,
  ] = await Promise.all([
    listClaimsByFilter({ includeInactive: true, limit: scanLimit + 1 }),
    listAllEntities(scanLimit + 1),
    listAllRelations(scanLimit + 1),
    readClaimLinks(),
    readClaimEntities(),
    readActiveContextItems(),
  ]);
  const claimsTruncated = claimsLoaded.length > scanLimit;
  const entitiesTruncated = entitiesLoaded.length > scanLimit;
  const relationsTruncated = relationsLoaded.length > scanLimit;
  const claims = claimsLoaded.slice(0, scanLimit);
  const entities = entitiesLoaded.slice(0, scanLimit);
  const relations = relationsLoaded.slice(0, scanLimit);

  const claimsById = new Map(claims.map((claim) => [claim.id, claim]));
  const entitiesById = new Map(entities.map((entity) => [entity.id, entity]));

  const claimsByEntityId = new Map<string, string[]>();
  const entitiesByClaimId = new Map<string, string[]>();
  for (const row of claimEntities) {
    if (!claimsById.has(row.claim_id) || !entitiesById.has(row.entity_id)) {
      continue;
    }
    const entityClaims = claimsByEntityId.get(row.entity_id) ?? [];
    entityClaims.push(row.claim_id);
    claimsByEntityId.set(row.entity_id, entityClaims);

    const claimEntitiesForClaim = entitiesByClaimId.get(row.claim_id) ?? [];
    claimEntitiesForClaim.push(row.entity_id);
    entitiesByClaimId.set(row.claim_id, claimEntitiesForClaim);
  }

  const claimAdjacency = new Map<string, Set<string>>();
  const directEvidence = new Map<string, Set<string>>();
  const contradictionGraph = new Map<string, Array<{ to: string; edge_id: string }>>();
  const supersedesGraph = new Map<string, Array<{ to: string; edge_id: string }>>();
  const entityDegree = new Map<string, number>();

  for (const claim of claims) {
    ensureClaimAdjacency(claimAdjacency, claim.id);
  }

  for (const link of claimLinks) {
    if (!claimsById.has(link.source_claim_id) || !claimsById.has(link.target_claim_id)) {
      continue;
    }
    addUndirectedClaimEdge(
      claimAdjacency,
      directEvidence,
      link.source_claim_id,
      link.target_claim_id,
      `claim_link:${link.id}:${link.link_type}`
    );
    if (link.link_type === 'contradicts') {
      addDirectedEdge(contradictionGraph, link.source_claim_id, link.target_claim_id, link.id);
    }
    if (link.link_type === 'supersedes') {
      addDirectedEdge(supersedesGraph, link.source_claim_id, link.target_claim_id, link.id);
    }
  }

  for (const [entityId, connectedClaims] of claimsByEntityId.entries()) {
    const uniqueClaims = sortedUnique(connectedClaims);
    if (uniqueClaims.length > 0) {
      const degree = entityDegree.get(entityId) ?? 0;
      entityDegree.set(entityId, degree + uniqueClaims.length);
    }
    for (let leftIndex = 0; leftIndex < uniqueClaims.length; leftIndex++) {
      for (let rightIndex = leftIndex + 1; rightIndex < uniqueClaims.length; rightIndex++) {
        addUndirectedClaimEdge(
          claimAdjacency,
          directEvidence,
          uniqueClaims[leftIndex]!,
          uniqueClaims[rightIndex]!,
          `shared_entity:${entityId}`
        );
      }
    }
  }

  for (const relation of relations) {
    const leftClaims = claimsByEntityId.get(relation.src_id) ?? [];
    const rightClaims = claimsByEntityId.get(relation.dst_id) ?? [];
    const leftUnique = sortedUnique(leftClaims);
    const rightUnique = sortedUnique(rightClaims);
    const relationDegree = entityDegree.get(relation.src_id) ?? 0;
    entityDegree.set(relation.src_id, relationDegree + 1);
    const reverseDegree = entityDegree.get(relation.dst_id) ?? 0;
    entityDegree.set(relation.dst_id, reverseDegree + 1);

    for (const leftClaim of leftUnique) {
      for (const rightClaim of rightUnique) {
        addUndirectedClaimEdge(
          claimAdjacency,
          directEvidence,
          leftClaim,
          rightClaim,
          `relation:${relation.id}:${relation.type}`
        );
      }
    }
  }

  const components = buildComponents(claimsById, claimAdjacency);
  const orphanClaims = claims.filter(
    (claim) =>
      (claimAdjacency.get(claim.id)?.size ?? 0) === 0 &&
      (entitiesByClaimId.get(claim.id)?.length ?? 0) === 0
  );
  const orphanEntities = entities.filter((entity) => {
    const claimCount = claimsByEntityId.get(entity.id)?.length ?? 0;
    const relationCount = entityDegree.get(entity.id) ?? 0;
    return claimCount === 0 && relationCount === 0;
  });

  const contradictionCycles = findContradictionCycles(contradictionGraph);
  const supersessionChains = findSupersessionChains(supersedesGraph, minSupersessionChainLength);
  const scopeHoleFindings = buildScopeHoleFindings(components);
  const repeatedCoactivationFindings = findRepeatedCoactivations(
    activeContextItems,
    directEvidence,
    repeatedCoactivationThreshold
  );
  const genericHubFindings = findGenericHubs({
    claims,
    entities,
    claimAdjacency,
    entitiesByClaimId,
    entityDegree,
    genericHubDegreeThreshold,
  });

  const findings = limitFindingsPerKind(
    [
      ...orphanClaims.map((claim) => ({
        kind: 'orphan_claim' as const,
        severity: 'warning' as const,
        message: `Claim ${claim.id} is disconnected from the graph substrate`,
        node_ids: [claim.id],
        details: {
          scope: claim.scope,
          kind: claim.kind,
        },
      })),
      ...orphanEntities.map((entity) => ({
        kind: 'orphan_entity' as const,
        severity: 'warning' as const,
        message: `Entity ${entity.id} has no claim or relation attachments`,
        node_ids: [entity.id],
        details: {
          name: entity.name,
          type: entity.type,
        },
      })),
      ...contradictionCycles.map((cycle) => ({
        kind: 'contradiction_cycle' as const,
        severity: 'critical' as const,
        message: `Contradiction cycle detected across ${cycle.nodes.length} claims`,
        node_ids: cycle.nodes,
        edge_ids: cycle.edge_ids,
        details: {
          cycle: cycle.nodes,
        },
      })),
      ...supersessionChains.map((chain) => ({
        kind: 'supersession_chain' as const,
        severity: 'warning' as const,
        message: `Supersession chain length ${chain.edge_ids.length} exceeds the audit threshold`,
        node_ids: chain.nodes,
        edge_ids: chain.edge_ids,
        details: {
          chain_length: chain.edge_ids.length,
        },
      })),
      ...scopeHoleFindings,
      ...repeatedCoactivationFindings,
      ...genericHubFindings,
    ],
    maxFindingsPerKind
  );

  return {
    summary: {
      claims: claims.length,
      entities: entities.length,
      relations: relations.length,
      claim_links: claimLinks.length,
      components: components.length,
      orphan_claims: orphanClaims.length,
      orphan_entities: orphanEntities.length,
      contradiction_cycles: contradictionCycles.length,
      supersession_chains: supersessionChains.length,
      scope_holes: scopeHoleFindings.length,
      repeated_coactivations: repeatedCoactivationFindings.length,
      generic_hubs: genericHubFindings.length,
      truncated: claimsTruncated || entitiesTruncated || relationsTruncated,
    },
    truncation: {
      claims: claimsTruncated,
      entities: entitiesTruncated,
      relations: relationsTruncated,
    },
    findings,
    components,
  };
}

async function readClaimLinks(): Promise<ClaimLinkRow[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT id, source_claim_id, target_claim_id, link_type FROM claim_links'
  );
  return reader.getRowObjects() as unknown as ClaimLinkRow[];
}

async function readClaimEntities(): Promise<ClaimEntityRow[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT claim_id, entity_id FROM claim_entities');
  return reader.getRowObjects() as unknown as ClaimEntityRow[];
}

async function readActiveContextItems(): Promise<ActiveContextItemRow[]> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    'SELECT active_context_id, claim_id FROM active_context_items'
  );
  return reader.getRowObjects() as unknown as ActiveContextItemRow[];
}

function buildComponents(
  claimsById: Map<string, Claim>,
  adjacency: Map<string, Set<string>>
): GraphAuditComponent[] {
  const visited = new Set<string>();
  const components: GraphAuditComponent[] = [];

  for (const claim of claimsById.values()) {
    if (visited.has(claim.id)) {
      continue;
    }

    const queue = [claim.id];
    const members: string[] = [];
    visited.add(claim.id);

    while (queue.length > 0) {
      const current = queue.shift();
      if (!current) {
        continue;
      }
      members.push(current);
      for (const neighbor of adjacency.get(current) ?? []) {
        if (visited.has(neighbor)) {
          continue;
        }
        visited.add(neighbor);
        queue.push(neighbor);
      }
    }

    const scopeCounts = members.reduce<Record<string, number>>((acc, claimId) => {
      const scope = claimsById.get(claimId)?.scope ?? 'unknown';
      acc[scope] = (acc[scope] ?? 0) + 1;
      return acc;
    }, {});

    const missingScopes = [];
    if ((scopeCounts['project'] ?? 0) > 0 && (scopeCounts['principle'] ?? 0) === 0) {
      missingScopes.push('principle');
    }
    if (
      (scopeCounts['session'] ?? 0) > 0 &&
      (scopeCounts['project'] ?? 0) === 0 &&
      (scopeCounts['principle'] ?? 0) === 0
    ) {
      missingScopes.push('project');
      missingScopes.push('principle');
    }

    components.push({
      id: componentIdForIndex(components.length),
      claim_ids: members.sort(),
      scope_counts: scopeCounts,
      missing_scopes: sortedUnique(missingScopes),
    });
  }

  return components;
}

function findContradictionCycles(
  adjacency: Map<string, Array<{ to: string; edge_id: string }>>
): Array<{ nodes: string[]; edge_ids: string[] }> {
  const seen = new Set<string>();
  const cycles: Array<{ nodes: string[]; edge_ids: string[] }> = [];

  const nodes = [...adjacency.keys()].sort();
  for (const start of nodes) {
    const stackNodes: string[] = [start];
    const stackEdges: string[] = [];
    const visiting = new Set<string>([start]);

    const dfs = (current: string): void => {
      for (const edge of adjacency.get(current) ?? []) {
        if (edge.to === start && stackNodes.length > 1) {
          const cycleNodes = [...stackNodes];
          const key = canonicalizeCycle(cycleNodes);
          if (!seen.has(key)) {
            seen.add(key);
            cycles.push({
              nodes: [...cycleNodes, start],
              edge_ids: [...stackEdges, edge.edge_id],
            });
          }
          continue;
        }
        if (visiting.has(edge.to) || edge.to < start) {
          continue;
        }
        visiting.add(edge.to);
        stackNodes.push(edge.to);
        stackEdges.push(edge.edge_id);
        dfs(edge.to);
        stackEdges.pop();
        stackNodes.pop();
        visiting.delete(edge.to);
      }
    };

    dfs(start);
  }

  return cycles;
}

function findSupersessionChains(
  adjacency: Map<string, Array<{ to: string; edge_id: string }>>,
  minLength: number
): Array<{ nodes: string[]; edge_ids: string[] }> {
  const incoming = new Map<string, number>();
  for (const [from, edges] of adjacency.entries()) {
    if (!incoming.has(from)) {
      incoming.set(from, 0);
    }
    for (const edge of edges) {
      incoming.set(edge.to, (incoming.get(edge.to) ?? 0) + 1);
    }
  }

  const roots = [...adjacency.keys()].filter((node) => (incoming.get(node) ?? 0) === 0);
  const memo = new Map<string, SupersessionPath | undefined>();
  const chains: Array<{ nodes: string[]; edge_ids: string[] }> = [];

  for (const root of roots.sort()) {
    const path = chooseLongestPathFromRoot(root, adjacency, new Set<string>(), memo);
    if (!path || path.edge_ids.length < minLength) {
      continue;
    }
    chains.push({
      nodes: path.nodes,
      edge_ids: path.edge_ids,
    });
  }

  return chains;
}

function buildScopeHoleFindings(components: GraphAuditComponent[]): GraphAuditFinding[] {
  const findings: GraphAuditFinding[] = [];
  for (const component of components) {
    if (component.missing_scopes.length === 0) {
      continue;
    }
    findings.push({
      kind: 'scope_hole',
      severity: component.missing_scopes.includes('principle') ? 'warning' : 'info',
      message: `Component ${component.id} is missing expected scope anchors: ${component.missing_scopes.join(', ')}`,
      node_ids: component.claim_ids,
      details: {
        component_id: component.id,
        scope_counts: component.scope_counts,
        missing_scopes: component.missing_scopes,
      },
    });
  }
  return findings;
}

function findRepeatedCoactivations(
  activeContextItems: ActiveContextItemRow[],
  directEvidence: Map<string, Set<string>>,
  threshold: number
): GraphAuditFinding[] {
  const contexts = new Map<string, Set<string>>();
  for (const row of activeContextItems) {
    const claims = contexts.get(row.active_context_id) ?? new Set<string>();
    claims.add(row.claim_id);
    contexts.set(row.active_context_id, claims);
  }

  const coactivationCounts = new Map<string, { count: number; context_ids: Set<string> }>();
  for (const [contextId, claims] of contexts.entries()) {
    const claimIds = [...claims].sort();
    for (let leftIndex = 0; leftIndex < claimIds.length; leftIndex++) {
      for (let rightIndex = leftIndex + 1; rightIndex < claimIds.length; rightIndex++) {
        const key = pairKey(claimIds[leftIndex]!, claimIds[rightIndex]!);
        const current = coactivationCounts.get(key) ?? {
          count: 0,
          context_ids: new Set<string>(),
        };
        current.count += 1;
        current.context_ids.add(contextId);
        coactivationCounts.set(key, current);
      }
    }
  }

  const findings: GraphAuditFinding[] = [];
  for (const [key, value] of [...coactivationCounts.entries()].sort((left, right) => {
    if (right[1].count !== left[1].count) {
      return right[1].count - left[1].count;
    }
    return left[0].localeCompare(right[0]);
  })) {
    if (value.count < threshold || directEvidence.has(key)) {
      continue;
    }
    const [left, right] = key.split('::');
    if (!left || !right) {
      continue;
    }
    findings.push({
      kind: 'repeated_coactivation',
      severity: 'warning',
      message: `Claims ${left} and ${right} co-activate ${value.count} times without a direct graph edge`,
      node_ids: [left, right],
      context_ids: sortedUnique(value.context_ids),
      details: {
        coactivation_count: value.count,
        threshold,
      },
    });
  }

  return findings;
}

function findGenericHubs(input: {
  claims: Claim[];
  entities: EntityRow[];
  claimAdjacency: Map<string, Set<string>>;
  entitiesByClaimId: Map<string, string[]>;
  entityDegree: Map<string, number>;
  genericHubDegreeThreshold: number;
}): GraphAuditFinding[] {
  const findings: GraphAuditFinding[] = [];

  for (const claim of input.claims) {
    const degree = input.claimAdjacency.get(claim.id)?.size ?? 0;
    if (degree < input.genericHubDegreeThreshold) {
      continue;
    }
    if (!isGenericLabel(claim.text)) {
      continue;
    }
    findings.push({
      kind: 'generic_hub',
      severity: 'info',
      message: `Claim ${claim.id} looks like a generic hub with degree ${degree}`,
      node_ids: [claim.id],
      details: {
        node_type: 'claim',
        degree,
        text_preview: claim.text.slice(0, 120),
      },
    });
  }

  for (const entity of input.entities) {
    const degree =
      (input.entitiesByClaimId.get(entity.id)?.length ?? 0) +
      (input.entityDegree.get(entity.id) ?? 0);
    if (degree < input.genericHubDegreeThreshold) {
      continue;
    }
    if (!isGenericLabel(entity.name)) {
      continue;
    }
    findings.push({
      kind: 'generic_hub',
      severity: 'info',
      message: `Entity ${entity.id} looks like a generic hub with degree ${degree}`,
      node_ids: [entity.id],
      details: {
        node_type: 'entity',
        degree,
        name: entity.name,
      },
    });
  }

  return findings;
}

import { computeContentHash } from '@pce/embeddings';
import {
  findEntityByCanonicalKey,
  findEntityByName,
  linkClaimEntity,
  upsertEntity,
  type EntityInput,
} from './entities.js';
import { upsertRelation } from './relations.js';

export type EntityCandidateType = 'identifier' | 'file' | 'term' | 'config' | 'package';

export interface EntityCandidate {
  name: string;
  canonical_key: string;
  type: EntityCandidateType;
  graph_type: EntityInput['type'];
  aliases: string[];
}

export interface AutoEntityGraphResult {
  entityCount: number;
  entityFailed: number;
  relationCount: number;
  relationFailed: number;
  entityIds: string[];
}

type DetectionSeed = {
  name: string;
  canonical_key: string;
  type: EntityCandidateType;
  graph_type: EntityInput['type'];
};

type DetectionMatch = DetectionSeed & {
  alias: string;
  index: number;
  end: number;
};

const FILE_EXTENSION_PATTERN =
  '(?:ts|tsx|js|jsx|mjs|cjs|json|yaml|yml|md|sql|tla|cfg|sh|py|go|rs|java|kt|swift)';
const FILE_PATH_REGEX = new RegExp(
  String.raw`(^|[\s([{"'\`])((?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.${FILE_EXTENSION_PATTERN})(?=$|[\s)\]}",:;'"\`])`,
  'g'
);
const SCOPED_PACKAGE_REGEX =
  /(^|[^A-Za-z0-9@/_-])(@[a-z0-9][a-z0-9._-]*\/[a-z0-9][a-z0-9._-]*)(?=$|[^A-Za-z0-9/_-])/g;
const CONFIG_REGEX = /\b(?:[A-Z][A-Z0-9]*(?:_[A-Z0-9]+)+|[A-Z][A-Z0-9]{2,})\b/g;
const CAMEL_CASE_REGEX = /\b[a-z]+(?:[A-Z][A-Za-z0-9]*)+\b/g;
const PASCAL_CASE_REGEX = /\b[A-Z][A-Za-z0-9]*[a-z][A-Za-z0-9]*[A-Z][A-Za-z0-9]*\b/g;
const PACKAGE_LITERALS = ['pce-memory'] as const;
const TECHNICAL_TERMS = [
  { name: 'JWT', canonical_key: 'jwt', type: 'term', graph_type: 'Concept' },
  { name: 'MCP', canonical_key: 'mcp', type: 'term', graph_type: 'Concept' },
  { name: 'CRDT', canonical_key: 'crdt', type: 'term', graph_type: 'Concept' },
  { name: 'DuckDB', canonical_key: 'duckdb', type: 'term', graph_type: 'Concept' },
  { name: 'TypeScript', canonical_key: 'typescript', type: 'term', graph_type: 'Concept' },
  { name: 'fp-ts', canonical_key: 'fp-ts', type: 'term', graph_type: 'Concept' },
  { name: 'Vitest', canonical_key: 'vitest', type: 'term', graph_type: 'Concept' },
  { name: 'pnpm', canonical_key: 'pnpm', type: 'term', graph_type: 'Concept' },
  { name: 'tsx', canonical_key: 'tsx', type: 'term', graph_type: 'Concept' },
] as const;
const DETECTION_PRIORITY: Record<EntityCandidateType, number> = {
  file: 5,
  package: 4,
  config: 3,
  term: 2,
  identifier: 1,
};

function normalizeWhitespace(value: string): string {
  return value.replace(/\s+/g, ' ').trim();
}

function normalizeFilePath(value: string): string {
  return value.replace(/\\/g, '/').replace(/^\.\//, '').replace(/\/+/g, '/').toLowerCase();
}

function normalizeConstant(value: string): string {
  return value.trim().toLowerCase();
}

function normalizeIdentifier(value: string): string {
  return value.trim().toLowerCase();
}

function normalizePackageName(value: string): string {
  return value.trim().toLowerCase();
}

function buildLiteralPattern(literal: string): RegExp {
  const escaped = literal.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  return new RegExp(`(^|[^A-Za-z0-9@/_-])(${escaped})(?=$|[^A-Za-z0-9/_-])`, 'gi');
}

function isInsideOccupiedRange(
  start: number,
  end: number,
  occupiedRanges: ReadonlyArray<{ start: number; end: number }>
): boolean {
  return occupiedRanges.some((range) => start < range.end && end > range.start);
}

function registerCandidate(
  candidates: Map<string, EntityCandidate>,
  match: DetectionMatch,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  const alias = normalizeWhitespace(match.alias);
  if (alias.length === 0) {
    return;
  }

  const existing = candidates.get(match.canonical_key);
  if (!existing) {
    candidates.set(match.canonical_key, {
      name: match.name,
      canonical_key: match.canonical_key,
      type: match.type,
      graph_type: match.graph_type,
      aliases: [alias],
    });
    occupiedRanges.push({ start: match.index, end: match.end });
    return;
  }

  const nextAliases = existing.aliases.includes(alias)
    ? existing.aliases
    : [...existing.aliases, alias];
  const shouldReplace = DETECTION_PRIORITY[match.type] > DETECTION_PRIORITY[existing.type];
  candidates.set(match.canonical_key, {
    name: shouldReplace ? match.name : existing.name,
    canonical_key: existing.canonical_key,
    type: shouldReplace ? match.type : existing.type,
    graph_type: shouldReplace ? match.graph_type : existing.graph_type,
    aliases: nextAliases,
  });
}

function detectFilePaths(
  text: string,
  candidates: Map<string, EntityCandidate>,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  for (const match of text.matchAll(FILE_PATH_REGEX)) {
    const alias = match[2];
    if (!alias) {
      continue;
    }
    const offset = match[1]?.length ?? 0;
    const index = (match.index ?? 0) + offset;
    registerCandidate(
      candidates,
      {
        name: alias,
        canonical_key: normalizeFilePath(alias),
        type: 'file',
        graph_type: 'Artifact',
        alias,
        index,
        end: index + alias.length,
      },
      occupiedRanges
    );
  }
}

function detectScopedPackages(
  text: string,
  candidates: Map<string, EntityCandidate>,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  for (const match of text.matchAll(SCOPED_PACKAGE_REGEX)) {
    const alias = match[2];
    if (!alias) {
      continue;
    }
    const offset = match[1]?.length ?? 0;
    const index = (match.index ?? 0) + offset;
    registerCandidate(
      candidates,
      {
        name: alias,
        canonical_key: normalizePackageName(alias),
        type: 'package',
        graph_type: 'Artifact',
        alias,
        index,
        end: index + alias.length,
      },
      occupiedRanges
    );
  }
}

function detectLiteralSeeds(
  text: string,
  seeds: readonly DetectionSeed[],
  candidates: Map<string, EntityCandidate>,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  for (const seed of seeds) {
    const pattern = buildLiteralPattern(seed.name);
    for (const match of text.matchAll(pattern)) {
      const alias = match[2];
      if (!alias) {
        continue;
      }
      const offset = match[1]?.length ?? 0;
      const index = (match.index ?? 0) + offset;
      registerCandidate(
        candidates,
        {
          ...seed,
          alias,
          index,
          end: index + alias.length,
        },
        occupiedRanges
      );
    }
  }
}

function detectConfigConstants(
  text: string,
  candidates: Map<string, EntityCandidate>,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  for (const match of text.matchAll(CONFIG_REGEX)) {
    const alias = match[0];
    const index = match.index ?? 0;
    const end = index + alias.length;
    if (isInsideOccupiedRange(index, end, occupiedRanges)) {
      continue;
    }
    registerCandidate(
      candidates,
      {
        name: alias,
        canonical_key: normalizeConstant(alias),
        type: 'config',
        graph_type: 'Concept',
        alias,
        index,
        end,
      },
      occupiedRanges
    );
  }
}

function detectIdentifiers(
  regex: RegExp,
  text: string,
  candidates: Map<string, EntityCandidate>,
  occupiedRanges: Array<{ start: number; end: number }>
): void {
  for (const match of text.matchAll(regex)) {
    const alias = match[0];
    const index = match.index ?? 0;
    const end = index + alias.length;
    if (isInsideOccupiedRange(index, end, occupiedRanges)) {
      continue;
    }
    registerCandidate(
      candidates,
      {
        name: alias,
        canonical_key: normalizeIdentifier(alias),
        type: 'identifier',
        graph_type: 'Concept',
        alias,
        index,
        end,
      },
      occupiedRanges
    );
  }
}

export function extractEntities(text: string): EntityCandidate[] {
  const candidates = new Map<string, EntityCandidate>();
  const occupiedRanges: Array<{ start: number; end: number }> = [];

  detectFilePaths(text, candidates, occupiedRanges);
  detectScopedPackages(text, candidates, occupiedRanges);
  detectLiteralSeeds(
    text,
    PACKAGE_LITERALS.map((name) => ({
      name,
      canonical_key: normalizePackageName(name),
      type: 'package' as const,
      graph_type: 'Artifact' as const,
    })),
    candidates,
    occupiedRanges
  );
  detectLiteralSeeds(text, TECHNICAL_TERMS, candidates, occupiedRanges);
  detectConfigConstants(text, candidates, occupiedRanges);
  detectIdentifiers(CAMEL_CASE_REGEX, text, candidates, occupiedRanges);
  detectIdentifiers(PASCAL_CASE_REGEX, text, candidates, occupiedRanges);

  return [...candidates.values()].sort((left, right) =>
    left.canonical_key.localeCompare(right.canonical_key)
  );
}

function buildAutoEntityId(candidate: EntityCandidate): string {
  return `ent_auto_${computeContentHash(`${candidate.type}:${candidate.canonical_key}`).slice(0, 16)}`;
}

function buildCoOccursRelationId(
  claimId: string,
  leftEntityId: string,
  rightEntityId: string
): string {
  return `rel_auto_${computeContentHash(
    `co-occurs:${claimId}:${leftEntityId}:${rightEntityId}`
  ).slice(0, 16)}`;
}

async function resolveEntityId(candidate: EntityCandidate): Promise<string> {
  const byCanonical = await findEntityByCanonicalKey(candidate.canonical_key);
  if (byCanonical) {
    return byCanonical.id;
  }

  const byName = await findEntityByName(candidate.name);
  if (byName) {
    return byName.id;
  }

  const entity = await upsertEntity({
    id: buildAutoEntityId(candidate),
    type: candidate.graph_type,
    name: candidate.name,
    canonical_key: candidate.canonical_key,
    attrs: {
      auto: true,
      extractor: 'pattern-nlp',
      category: candidate.type,
      aliases: candidate.aliases,
    },
  });
  return entity.id;
}

export async function autoLinkClaimEntities(
  claimId: string,
  text: string
): Promise<AutoEntityGraphResult> {
  const extracted = extractEntities(text);
  const linkedEntityIds = new Set<string>();
  let entityCount = 0;
  let entityFailed = 0;
  let relationCount = 0;
  let relationFailed = 0;

  for (const candidate of extracted) {
    try {
      const entityId = await resolveEntityId(candidate);
      await linkClaimEntity(claimId, entityId);
      linkedEntityIds.add(entityId);
      entityCount++;
    } catch {
      entityFailed++;
    }
  }

  const orderedEntityIds = [...linkedEntityIds].sort();
  for (let i = 0; i < orderedEntityIds.length; i++) {
    for (let j = i + 1; j < orderedEntityIds.length; j++) {
      const srcId = orderedEntityIds[i]!;
      const dstId = orderedEntityIds[j]!;
      try {
        await upsertRelation({
          id: buildCoOccursRelationId(claimId, srcId, dstId),
          src_id: srcId,
          dst_id: dstId,
          type: 'co-occurs',
          evidence_claim_id: claimId,
          props: {
            auto: true,
            extractor: 'pattern-nlp',
          },
        });
        relationCount++;
      } catch {
        relationFailed++;
      }
    }
  }

  return {
    entityCount,
    entityFailed,
    relationCount,
    relationFailed,
    entityIds: orderedEntityIds,
  };
}

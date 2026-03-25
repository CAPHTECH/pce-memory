import { beforeEach, describe, expect, it } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import {
  autoLinkClaimEntities,
  extractEntities,
  type EntityCandidate,
} from '../src/store/entityExtractor';
import {
  findEntityByCanonicalKey,
  getEntitiesForClaim,
  upsertEntity,
} from '../src/store/entities';
import { queryRelations } from '../src/store/relations';

type BenchmarkSample = {
  text: string;
  expected: string[];
};

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
});

function byCanonicalKey(candidates: EntityCandidate[]): Map<string, EntityCandidate> {
  return new Map(candidates.map((candidate) => [candidate.canonical_key, candidate]));
}

function buildBenchmarkCorpus(): BenchmarkSample[] {
  const templates: BenchmarkSample[] = [
    {
      text: 'hybridSearch delegates ranking to DuckDB in src/store/hybridSearch.ts',
      expected: ['duckdb', 'hybridsearch', 'src/store/hybridsearch.ts'],
    },
    {
      text: 'handleActivate loads JWT policy from @pce/policy-schemas',
      expected: ['handleactivate', 'jwt', '@pce/policy-schemas'],
    },
    {
      text: 'PCE_DB tunes pce-memory startup for MCP clients',
      expected: ['pce_db', 'pce-memory', 'mcp'],
    },
    {
      text: 'Vitest exercises CRDT merge logic in src/sync/merge.ts',
      expected: ['vitest', 'crdt', 'src/sync/merge.ts'],
    },
    {
      text: 'TypeScript types for fp-ts adapters live in src/store/claimsEither.ts',
      expected: ['typescript', 'fp-ts', 'src/store/claimseither.ts'],
    },
    {
      text: 'K_TEXT and ALPHA adjust hybridSearch precision',
      expected: ['k_text', 'alpha', 'hybridsearch'],
    },
    {
      text: 'handlePromote syncs DuckDB evidence into pce-memory',
      expected: ['handlepromote', 'duckdb', 'pce-memory'],
    },
    {
      text: 'src/core/handlers.ts calls handleActivate during MCP bootstrap',
      expected: ['src/core/handlers.ts', 'handleactivate', 'mcp'],
    },
    {
      text: '@pce/policy-schemas keeps JWT defaults aligned with TypeScript',
      expected: ['@pce/policy-schemas', 'jwt', 'typescript'],
    },
    {
      text: 'PCE_DB and CRDT traces are asserted in Vitest',
      expected: ['pce_db', 'crdt', 'vitest'],
    },
  ];

  return Array.from({ length: 100 }, (_, index) => {
    const template = templates[index % templates.length]!;
    return {
      text: `${template.text} batch-${index + 1} release-2026.${(index % 12) + 1}`,
      expected: template.expected,
    };
  });
}

describe('extractEntities', () => {
  it('extracts PascalCase and camelCase identifiers', () => {
    const candidates = byCanonicalKey(
      extractEntities('hybridSearch delegates to handleActivate before DuckDB boots')
    );

    expect(candidates.get('hybridsearch')?.type).toBe('identifier');
    expect(candidates.get('handleactivate')?.type).toBe('identifier');
    expect(candidates.get('duckdb')?.type).toBe('term');
  });

  it('extracts file path entities', () => {
    const candidates = byCanonicalKey(
      extractEntities('src/store/hybridSearch.ts shares helpers with docs/schema.md')
    );

    expect(candidates.get('src/store/hybridsearch.ts')?.type).toBe('file');
    expect(candidates.get('docs/schema.md')?.type).toBe('file');
  });

  it('extracts technical terms from the dictionary', () => {
    const candidates = byCanonicalKey(extractEntities('JWT and MCP keep CRDT merges visible in Vitest'));

    expect(candidates.get('jwt')?.type).toBe('term');
    expect(candidates.get('mcp')?.type).toBe('term');
    expect(candidates.get('crdt')?.type).toBe('term');
    expect(candidates.get('vitest')?.type).toBe('term');
  });

  it('extracts config-like constants including underscore and flat uppercase names', () => {
    const candidates = byCanonicalKey(extractEntities('PCE_DB overrides ALPHA while K_TEXT stays fixed'));

    expect(candidates.get('pce_db')?.type).toBe('config');
    expect(candidates.get('alpha')?.type).toBe('config');
    expect(candidates.get('k_text')?.type).toBe('config');
  });

  it('extracts scoped and known package names', () => {
    const candidates = byCanonicalKey(
      extractEntities('@pce/policy-schemas feeds defaults into pce-memory')
    );

    expect(candidates.get('@pce/policy-schemas')?.type).toBe('package');
    expect(candidates.get('pce-memory')?.type).toBe('package');
  });
});

describe('autoLinkClaimEntities', () => {
  it('deduplicates against an existing graph entity via canonical_key', async () => {
    const { claim } = await upsertClaim({
      text: 'hybridSearch uses DuckDB for vector similarity',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:entity-extractor-dedup',
    });
    await upsertEntity({
      id: 'ent_manual_duckdb',
      type: 'Concept',
      name: 'DuckDB',
      canonical_key: 'duckdb',
    });

    const result = await autoLinkClaimEntities(claim.id, claim.text);
    const linkedEntities = await getEntitiesForClaim(claim.id);
    const duckdb = await findEntityByCanonicalKey('duckdb');

    expect(result.entityFailed).toBe(0);
    expect(duckdb?.id).toBe('ent_manual_duckdb');
    expect(linkedEntities.some((entity) => entity.id === 'ent_manual_duckdb')).toBe(true);
    expect(linkedEntities.filter((entity) => entity.canonical_key === 'duckdb')).toHaveLength(1);
  });

  it('creates co-occurs relations for entities extracted from the same claim', async () => {
    const { claim } = await upsertClaim({
      text: 'hybridSearch uses DuckDB with JWT rotation',
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: 'sha256:entity-extractor-co-occurs',
    });

    const result = await autoLinkClaimEntities(claim.id, claim.text);
    const relations = await queryRelations({
      evidence_claim_id: claim.id,
      type: 'co-occurs',
      limit: 10,
    });

    expect(result.entityCount).toBe(3);
    expect(result.relationCount).toBe(3);
    expect(relations).toHaveLength(3);
    expect(relations.every((relation) => relation.type === 'co-occurs')).toBe(true);
  });

  it('keeps precision and recall high across a 100-text benchmark corpus', () => {
    const corpus = buildBenchmarkCorpus();
    let truePositiveCount = 0;
    let falsePositiveCount = 0;
    let falseNegativeCount = 0;

    for (const sample of corpus) {
      const predicted = new Set(extractEntities(sample.text).map((candidate) => candidate.canonical_key));
      const expected = new Set(sample.expected);

      for (const value of predicted) {
        if (expected.has(value)) {
          truePositiveCount++;
        } else {
          falsePositiveCount++;
        }
      }

      for (const value of expected) {
        if (!predicted.has(value)) {
          falseNegativeCount++;
        }
      }
    }

    const precision =
      truePositiveCount / Math.max(truePositiveCount + falsePositiveCount, 1);
    const recall = truePositiveCount / Math.max(truePositiveCount + falseNegativeCount, 1);

    expect(precision).toBeGreaterThanOrEqual(0.95);
    expect(recall).toBeGreaterThanOrEqual(0.95);
  });
});

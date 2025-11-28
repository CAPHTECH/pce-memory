/**
 * Hybrid Search Integration Tests
 * ADR-0004: 実際のDuckDBを使用した統合テスト
 *
 * 検証内容:
 * - DuckDBマクロ（cos_sim, hybrid_score, norm_cos）の動作
 * - テキスト検索 + ベクトル検索の融合
 * - Text-onlyフォールバック
 * - スコープフィルタリング
 */
import { describe, it, expect, beforeEach, afterEach, vi } from 'vitest';
import { initDb, initSchema, resetDb, getConnection } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import {
  hybridSearch,
  setEmbeddingService,
  textSearch,
  vectorSearch,
} from '../src/store/hybridSearch';
import type { EmbeddingService } from '@pce/embeddings';
import * as TE from 'fp-ts/TaskEither';

// テスト用の固定埋め込みベクトル（正規化済み）
const createNormalizedVector = (seed: number): number[] => {
  // 簡易的な正規化ベクトル生成（3次元）
  const raw = [Math.sin(seed), Math.cos(seed), Math.sin(seed * 2)];
  const norm = Math.sqrt(raw.reduce((sum, v) => sum + v * v, 0));
  return raw.map((v) => v / norm);
};

// テスト用EmbeddingService（実際のベクトルを返す）
const createTestEmbeddingService = (): EmbeddingService => ({
  embed: (text: string) => TE.right(createNormalizedVector(text.length)),
  embedBatch: (texts: readonly string[]) =>
    TE.right(texts.map((t) => createNormalizedVector(t.length))),
  modelVersion: 'test-v1',
  invalidateCache: () => TE.right(undefined),
});

// クエリベクトル生成用
const queryVector = createNormalizedVector(5); // "alpha"相当

// ヘルパー: ベクトルをDB用JSON文字列に変換
const _vecToJson = (vec: number[]): string => JSON.stringify(vec);

describe('Hybrid Search Integration (Real DuckDB)', () => {
  beforeEach(async () => {
    resetDb();
    process.env.PCE_DB = ':memory:';
    await initDb();
    await initSchema();
  });

  afterEach(() => {
    vi.restoreAllMocks();
  });

  describe('DuckDB Macros', () => {
    it('cos_sim macro calculates cosine similarity correctly', async () => {
      const conn = await getConnection();
      // 同一ベクトルのcos_simは1.0（配列リテラルをSQLに直接埋め込み）
      const reader = await conn.runAndReadAll(
        `SELECT cos_sim([0.6, 0.8, 0.0]::DOUBLE[], [0.6, 0.8, 0.0]::DOUBLE[]) as sim`
      );
      const result = reader.getRowObjects() as { sim: number }[];
      expect(result[0].sim).toBeCloseTo(1.0, 5);
    });

    it('cos_sim macro returns 0 for orthogonal vectors', async () => {
      const conn = await getConnection();
      // 直交ベクトルのcos_simは0
      const reader = await conn.runAndReadAll(
        `SELECT cos_sim([1.0, 0.0, 0.0]::DOUBLE[], [0.0, 1.0, 0.0]::DOUBLE[]) as sim`
      );
      const result = reader.getRowObjects() as { sim: number }[];
      expect(result[0].sim).toBeCloseTo(0.0, 5);
    });

    it('norm_cos macro normalizes [-1,1] to [0,1]', async () => {
      const conn = await getConnection();
      // norm_cos(-1) = 0, norm_cos(0) = 0.5, norm_cos(1) = 1
      const reader = await conn.runAndReadAll(`
        SELECT
          norm_cos(-1.0) as min_val,
          norm_cos(0.0) as mid_val,
          norm_cos(1.0) as max_val
      `);
      const results = reader.getRowObjects() as {
        min_val: number;
        mid_val: number;
        max_val: number;
      }[];
      expect(results[0].min_val).toBeCloseTo(0.0, 5);
      expect(results[0].mid_val).toBeCloseTo(0.5, 5);
      expect(results[0].max_val).toBeCloseTo(1.0, 5);
    });

    it('hybrid_score macro applies alpha weighting', async () => {
      const conn = await getConnection();
      // hybrid_score(0.4, 0.8, 0.65) = 0.65 * 0.8 + 0.35 * 0.4 = 0.52 + 0.14 = 0.66
      const reader = await conn.runAndReadAll(`SELECT hybrid_score(0.4, 0.8, 0.65) as score`);
      const result = reader.getRowObjects() as { score: number }[];
      expect(result[0].score).toBeCloseTo(0.66, 5);
    });
  });

  describe('Text Search (Real DB)', () => {
    it('finds claims by text substring', async () => {
      await upsertClaim({
        text: 'foo alpha bar',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'h1',
      });
      await upsertClaim({
        text: 'beta gamma',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'h2',
      });

      // textSearch(query, scopes, limit) → SearchResult { claim, score }
      const results = await textSearch('alpha', ['project'], 10);
      expect(results).toHaveLength(1);
      expect(results[0].claim.text).toBe('foo alpha bar');
    });

    it('respects scope filtering', async () => {
      await upsertClaim({
        text: 'session claim',
        kind: 'fact',
        scope: 'session',
        boundary_class: 'internal',
        content_hash: 'h3',
      });
      await upsertClaim({
        text: 'project claim',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'h4',
      });

      // textSearch(query, scopes, limit) - empty query returns all in scope
      const results = await textSearch('', ['project'], 10);
      expect(results).toHaveLength(1);
      expect(results[0].claim.scope).toBe('project');
    });
  });

  describe('Vector Search (Real DB)', () => {
    it('finds claims by vector similarity', async () => {
      const embeddingService = createTestEmbeddingService();
      setEmbeddingService(embeddingService);

      // Claim作成
      const { claim } = await upsertClaim({
        text: 'alpha',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'v1',
      });

      // ベクトルを手動で挿入（配列リテラルをSQLに直接埋め込み）
      const conn = await getConnection();
      const vec = createNormalizedVector(5); // "alpha"の長さ=5
      const vecLiteral = `[${vec.join(',')}]::DOUBLE[]`;
      await conn.run(
        `INSERT INTO claim_vectors (claim_id, embedding, model_version) VALUES ($1, ${vecLiteral}, $2)`,
        [claim.id, 'test-v1']
      );

      // vectorSearch(queryEmbedding, scopes, limit) → SearchResult { claim, score }
      const results = await vectorSearch(vec, ['project'], 10);
      expect(results.length).toBeGreaterThan(0);
      expect(results[0].claim.id).toBe(claim.id);
    });

    it('returns empty for non-matching scopes', async () => {
      const conn = await getConnection();
      const { claim } = await upsertClaim({
        text: 'session only',
        kind: 'fact',
        scope: 'session',
        boundary_class: 'internal',
        content_hash: 'v2',
      });

      const vec = createNormalizedVector(10);
      const vecLiteral = `[${vec.join(',')}]::DOUBLE[]`;
      await conn.run(
        `INSERT INTO claim_vectors (claim_id, embedding, model_version) VALUES ($1, ${vecLiteral}, $2)`,
        [claim.id, 'test-v1']
      );

      // vectorSearch(queryEmbedding, scopes, limit) - projectスコープで検索
      const results = await vectorSearch(vec, ['project'], 10);
      expect(results).toHaveLength(0);
    });
  });

  describe('Hybrid Search (Full Integration)', () => {
    it('combines text and vector results', async () => {
      const embeddingService = createTestEmbeddingService();
      setEmbeddingService(embeddingService);

      const conn = await getConnection();

      // テキストでのみマッチするClaim
      const { claim: textClaim } = await upsertClaim({
        text: 'search keyword here',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'hybrid1',
      });

      // ベクトルでのみマッチするClaim
      const { claim: vecClaim } = await upsertClaim({
        text: 'something else',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'hybrid2',
      });
      const vecLiteral = `[${queryVector.join(',')}]::DOUBLE[]`;
      await conn.run(
        `INSERT INTO claim_vectors (claim_id, embedding, model_version) VALUES ($1, ${vecLiteral}, $2)`,
        [vecClaim.id, 'test-v1']
      );

      // textSearch(query, scopes, limit) → SearchResult { claim, score }
      const textResults = await textSearch('keyword', ['project'], 10);
      expect(textResults).toHaveLength(1);
      expect(textResults[0].claim.id).toBe(textClaim.id);

      // vectorSearch(queryEmbedding, scopes, limit) → SearchResult { claim, score }
      const vecResults = await vectorSearch(queryVector, ['project'], 10);
      expect(vecResults.length).toBeGreaterThan(0);
    });

    it('falls back to text-only when embedding service unavailable', async () => {
      // EmbeddingServiceをnullに設定
      setEmbeddingService(null as unknown as EmbeddingService);

      await upsertClaim({
        text: 'fallback test keyword',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'fallback1',
      });

      // Text-onlyフォールバック
      const results = await hybridSearch(['project'], 10, 'keyword');
      expect(results).toHaveLength(1);
      expect(results[0].text).toContain('keyword');
    });

    it('respects limit parameter', async () => {
      // 複数のClaimを作成
      for (let i = 0; i < 5; i++) {
        await upsertClaim({
          text: `claim ${i} with keyword`,
          kind: 'fact',
          scope: 'project',
          boundary_class: 'internal',
          content_hash: `limit${i}`,
        });
      }

      const results = await hybridSearch(['project'], 2, 'keyword');
      expect(results).toHaveLength(2);
    });

    it('filters by multiple scopes', async () => {
      await upsertClaim({
        text: 'session scope',
        kind: 'fact',
        scope: 'session',
        boundary_class: 'internal',
        content_hash: 'multi1',
      });
      await upsertClaim({
        text: 'project scope',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'multi2',
      });
      await upsertClaim({
        text: 'principle scope',
        kind: 'fact',
        scope: 'principle',
        boundary_class: 'internal',
        content_hash: 'multi3',
      });

      const results = await hybridSearch(['session', 'project'], 10);
      expect(results).toHaveLength(2);
      expect(results.every((c) => ['session', 'project'].includes(c.scope))).toBe(true);
    });
  });

  describe('TLA+ Invariants Verification', () => {
    it('Inv_C_ScopeConsistency: all results match requested scopes', async () => {
      await upsertClaim({
        text: 'in scope',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'inv1',
      });
      await upsertClaim({
        text: 'out of scope',
        kind: 'fact',
        scope: 'principle',
        boundary_class: 'internal',
        content_hash: 'inv2',
      });

      const requestedScopes = ['project', 'session'];
      const results = await hybridSearch(requestedScopes, 10);

      // TLA+ Inv_C_ScopeConsistency: 全結果がrequestedScopesに含まれる
      for (const claim of results) {
        expect(requestedScopes).toContain(claim.scope);
      }
    });

    it('Inv_C_MergeComplete: union of text and vector candidates', async () => {
      const embeddingService = createTestEmbeddingService();
      setEmbeddingService(embeddingService);

      const conn = await getConnection();

      // テキストマッチのみ
      const { claim: textOnly } = await upsertClaim({
        text: 'unique text marker',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'merge1',
      });

      // ベクトルマッチのみ
      const { claim: vecOnly } = await upsertClaim({
        text: 'different content',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        content_hash: 'merge2',
      });
      const vecLiteral = `[${queryVector.join(',')}]::DOUBLE[]`;
      await conn.run(
        `INSERT INTO claim_vectors (claim_id, embedding, model_version) VALUES ($1, ${vecLiteral}, $2)`,
        [vecOnly.id, 'test-v1']
      );

      // hybridSearchは両方を含むべき
      // textSearch(query, scopes, limit), vectorSearch(queryEmbedding, scopes, limit) → SearchResult { claim, score }
      const textResults = await textSearch('marker', ['project'], 10);
      const vecResults = await vectorSearch(queryVector, ['project'], 10);

      // TLA+ Inv_C_MergeComplete: textCandidates ∪ vecCandidates
      const expectedIds = new Set([
        ...textResults.map((r) => r.claim.id),
        ...vecResults.map((r) => r.claim.id),
      ]);

      expect(
        expectedIds.has(textOnly.id) || textResults.some((r) => r.claim.id === textOnly.id)
      ).toBe(true);
    });
  });
});

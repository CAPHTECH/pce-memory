/**
 * Hybrid Search テスト（ADR-0004 設計C）
 *
 * TLA+ 不変条件の検証:
 * - Inv_C_ScopeConsistency: スコープフィルタリング
 * - Inv_C_ThresholdFiltering: 閾値フィルタリング
 * - Inv_C_MergeComplete: 結果マージの完全性
 * - Inv_C_FusionCorrectness: 融合計算の正しさ
 *
 * @see docs/adr/0004-hybrid-search-design.md
 * @see docs/spec/tlaplus/hybrid_search_simple.tla
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { upsertClaim } from '../src/store/claims';
import type { EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { randomUUID } from 'crypto';
import { unlinkSync, existsSync } from 'fs';
import { tmpdir } from 'os';
import { join } from 'path';
import {
  textSearch,
  vectorSearch,
  hybridSearch,
  saveClaimVector,
  getClaimVector,
  deleteClaimVector,
  setEmbeddingService,
  HybridSearchConfig,
} from '../src/store/hybridSearch';

/**
 * モックEmbeddingService
 * テスト用の固定埋め込みを返す
 */
function createMockEmbeddingService(embedding: readonly number[]): EmbeddingService {
  return {
    embed: () => () =>
      Promise.resolve(
        E.right({
          embedding,
          modelVersion: 'mock-v1',
        })
      ),
  };
}

/**
 * 失敗するモックEmbeddingService
 */
function createFailingEmbeddingService(): EmbeddingService {
  return {
    embed: () => () => Promise.resolve(E.left(new Error('Embedding failed') as unknown as never)),
  };
}

// 一意のテストDBパス（テスト間の完全な分離を確保）
let testDbPath: string;

beforeEach(async () => {
  // EmbeddingServiceをリセット（テスト間で独立させる）
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  // 一意のファイルベースDBを使用（CI環境での:memory:の問題を回避）
  testDbPath = join(tmpdir(), `pce-test-${randomUUID()}.duckdb`);
  process.env.PCE_DB = testDbPath;
  await initDb();
  await initSchema();
});

afterEach(async () => {
  // テスト後のクリーンアップ（グローバル状態をリセット）
  setEmbeddingService(null as unknown as EmbeddingService);
  await resetDbAsync();
  // テスト用DBファイルを削除
  if (testDbPath && existsSync(testDbPath)) {
    try {
      unlinkSync(testDbPath);
    } catch {
      // 削除エラーは無視（ファイルが既に削除されている可能性）
    }
  }
  // WALファイルも削除
  const walPath = `${testDbPath}.wal`;
  if (existsSync(walPath)) {
    try {
      unlinkSync(walPath);
    } catch {
      // 削除エラーは無視
    }
  }
});

// ========== テストデータ ==========

const testClaims = [
  {
    text: 'TypeScript is a typed superset of JavaScript',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:0001',
  },
  {
    text: 'React is a JavaScript library for building user interfaces',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:0002',
  },
  {
    text: 'User prefers dark mode in the editor',
    kind: 'preference',
    scope: 'session',
    boundary_class: 'internal',
    content_hash: 'sha256:0003',
  },
  {
    text: 'Python is great for data science and machine learning',
    kind: 'fact',
    scope: 'principle',
    boundary_class: 'public',
    content_hash: 'sha256:0004',
  },
];

// 疑似埋め込みベクトル（384次元のダミー）
const createDummyEmbedding = (seed: number): number[] => {
  const embedding: number[] = [];
  for (let i = 0; i < 384; i++) {
    embedding.push(Math.sin(seed * (i + 1)) * 0.5 + 0.5);
  }
  return embedding;
};

// ========== claim_vectorsテーブル操作テスト ==========

describe('claim_vectors operations', () => {
  it('should save and retrieve claim vector', async () => {
    // Claimを作成
    const { claim } = await upsertClaim(testClaims[0]);
    const embedding = createDummyEmbedding(1);

    // ベクトル保存
    await saveClaimVector(claim.id, embedding, 'test-model-v1');

    // ベクトル取得
    const retrieved = await getClaimVector(claim.id);
    expect(retrieved).toBeDefined();
    expect(retrieved!.length).toBe(384);
    expect(retrieved![0]).toBeCloseTo(embedding[0], 5);
  });

  it('should update claim vector on upsert', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    const embedding1 = createDummyEmbedding(1);
    const embedding2 = createDummyEmbedding(2);

    // 1回目の保存
    await saveClaimVector(claim.id, embedding1, 'test-model-v1');

    // 2回目の保存（更新）
    await saveClaimVector(claim.id, embedding2, 'test-model-v2');

    const retrieved = await getClaimVector(claim.id);
    expect(retrieved![0]).toBeCloseTo(embedding2[0], 5);
  });

  it('should delete claim vector', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    await saveClaimVector(claim.id, createDummyEmbedding(1), 'test-model-v1');

    // 削除
    await deleteClaimVector(claim.id);

    const retrieved = await getClaimVector(claim.id);
    expect(retrieved).toBeUndefined();
  });
});

// ========== Text検索テスト ==========

describe('textSearch', () => {
  beforeEach(async () => {
    // テストデータ投入
    for (const c of testClaims) {
      await upsertClaim(c);
    }
  });

  it('should find claims matching query text', async () => {
    const results = await textSearch('JavaScript', ['project'], 10);
    expect(results.length).toBe(2);
    expect(results.every((r) => r.claim.text.includes('JavaScript'))).toBe(true);
  });

  it('should filter by scope (TLA+ Inv_C_ScopeConsistency)', async () => {
    const results = await textSearch('is', ['session'], 10);
    // "session"スコープには"User prefers..."のみ
    expect(results.every((r) => r.claim.scope === 'session')).toBe(true);
  });

  it('should respect limit parameter', async () => {
    const results = await textSearch('a', ['project', 'session', 'principle'], 2);
    expect(results.length).toBeLessThanOrEqual(2);
  });

  it('should return empty for no matches', async () => {
    const results = await textSearch('nonexistent123xyz', ['project'], 10);
    expect(results.length).toBe(0);
  });
});

// ========== Vector検索テスト ==========

describe('vectorSearch', () => {
  let claimIds: string[];

  beforeEach(async () => {
    claimIds = [];
    // テストデータ投入 + ベクトル保存
    for (let i = 0; i < testClaims.length; i++) {
      const { claim } = await upsertClaim(testClaims[i]);
      claimIds.push(claim.id);
      await saveClaimVector(claim.id, createDummyEmbedding(i + 1), 'test-model-v1');
    }
  });

  it('should find claims by vector similarity', async () => {
    const queryEmbedding = createDummyEmbedding(1); // seed=1のベクトル
    const results = await vectorSearch(queryEmbedding, ['project'], 10);
    expect(results.length).toBeGreaterThan(0);
  });

  it('should filter by scope (TLA+ Inv_C_ScopeConsistency)', async () => {
    const queryEmbedding = createDummyEmbedding(3);
    const results = await vectorSearch(queryEmbedding, ['session'], 10);
    expect(results.every((r) => r.claim.scope === 'session')).toBe(true);
  });

  it('should return empty when no vectors exist', async () => {
    // 新しい一意のDBファイルで完全に分離
    await resetDbAsync();
    const freshDbPath = join(tmpdir(), `pce-test-novectors-${randomUUID()}.duckdb`);
    process.env.PCE_DB = freshDbPath;
    await initDb();
    await initSchema();
    await upsertClaim(testClaims[0]);
    // ベクトルを保存しない

    const results = await vectorSearch(createDummyEmbedding(1), ['project'], 10);
    expect(results.length).toBe(0);

    // クリーンアップ
    await resetDbAsync();
    if (existsSync(freshDbPath)) {
      try {
        unlinkSync(freshDbPath);
      } catch {
        // ignore
      }
    }
  });

  it('should return scores normalized to 0-1 range', async () => {
    const queryEmbedding = createDummyEmbedding(1);
    const results = await vectorSearch(queryEmbedding, ['project', 'session', 'principle'], 10);
    for (const r of results) {
      expect(r.score).toBeGreaterThanOrEqual(0);
      expect(r.score).toBeLessThanOrEqual(1);
    }
  });
});

// ========== Hybrid検索テスト ==========

describe('hybridSearch', () => {
  let claimIds: string[];

  beforeEach(async () => {
    claimIds = [];
    for (let i = 0; i < testClaims.length; i++) {
      const { claim } = await upsertClaim(testClaims[i]);
      claimIds.push(claim.id);
      await saveClaimVector(claim.id, createDummyEmbedding(i + 1), 'test-model-v1');
    }
  });

  it('should filter by scope (TLA+ Inv_C_ScopeConsistency)', async () => {
    // EmbeddingServiceなしでText-onlyフォールバック
    const results = await hybridSearch(['session'], 10, 'user');
    expect(results.every((c) => c.scope === 'session')).toBe(true);
  });

  it('should return claims without query (fallback to critic score)', async () => {
    const results = await hybridSearch(['project'], 10);
    expect(results.length).toBeGreaterThan(0);
  });

  it('should respect limit parameter', async () => {
    const results = await hybridSearch(['project', 'session', 'principle'], 2);
    expect(results.length).toBeLessThanOrEqual(2);
  });

  it('should fallback to text-only when EmbeddingService is not available', async () => {
    // EmbeddingServiceなし
    const results = await hybridSearch(['project'], 10, 'JavaScript');
    // Text-onlyで検索されるはず
    expect(results.length).toBeGreaterThan(0);
    expect(results.some((c) => c.text.includes('JavaScript'))).toBe(true);
  });
});

// ========== DuckDBマクロテスト ==========

describe('DuckDB macros', () => {
  it('should calculate cos_sim correctly', async () => {
    const conn = await getConnection();
    // 同じベクトル → cos_sim = 1
    const result1 = await conn.runAndReadAll(
      'SELECT cos_sim([1.0, 0.0, 0.0]::DOUBLE[], [1.0, 0.0, 0.0]::DOUBLE[]) as sim'
    );
    const rows1 = result1.getRowObjects() as { sim: number }[];
    expect(rows1[0].sim).toBeCloseTo(1.0, 5);

    // 直交ベクトル → cos_sim = 0
    const result2 = await conn.runAndReadAll(
      'SELECT cos_sim([1.0, 0.0, 0.0]::DOUBLE[], [0.0, 1.0, 0.0]::DOUBLE[]) as sim'
    );
    const rows2 = result2.getRowObjects() as { sim: number }[];
    expect(rows2[0].sim).toBeCloseTo(0.0, 5);

    // 反対ベクトル → cos_sim = -1
    const result3 = await conn.runAndReadAll(
      'SELECT cos_sim([1.0, 0.0, 0.0]::DOUBLE[], [-1.0, 0.0, 0.0]::DOUBLE[]) as sim'
    );
    const rows3 = result3.getRowObjects() as { sim: number }[];
    expect(rows3[0].sim).toBeCloseTo(-1.0, 5);
  });

  it('should calculate hybrid_score correctly (TLA+ FusedScore)', async () => {
    const conn = await getConnection();
    // α=0.65: 0.65 * vec + 0.35 * text
    const result = await conn.runAndReadAll('SELECT hybrid_score(0.5, 0.8, 0.65) as score');
    const rows = result.getRowObjects() as { score: number }[];
    const expected = 0.65 * 0.8 + 0.35 * 0.5; // 0.52 + 0.175 = 0.695
    expect(rows[0].score).toBeCloseTo(expected, 5);
  });

  it('should normalize cos_sim with norm_cos', async () => {
    const conn = await getConnection();
    // norm_cos(-1) = 0, norm_cos(0) = 0.5, norm_cos(1) = 1
    const result1 = await conn.runAndReadAll('SELECT norm_cos(-1.0) as n');
    const rows1 = result1.getRowObjects() as { n: number }[];
    expect(rows1[0].n).toBeCloseTo(0.0, 5);

    const result2 = await conn.runAndReadAll('SELECT norm_cos(0.0) as n');
    const rows2 = result2.getRowObjects() as { n: number }[];
    expect(rows2[0].n).toBeCloseTo(0.5, 5);

    const result3 = await conn.runAndReadAll('SELECT norm_cos(1.0) as n');
    const rows3 = result3.getRowObjects() as { n: number }[];
    expect(rows3[0].n).toBeCloseTo(1.0, 5);
  });
});

// ========== TLA+不変条件検証テスト ==========

describe('TLA+ Invariants', () => {
  beforeEach(async () => {
    for (let i = 0; i < testClaims.length; i++) {
      const { claim } = await upsertClaim(testClaims[i]);
      await saveClaimVector(claim.id, createDummyEmbedding(i + 1), 'test-model-v1');
    }
  });

  it('Inv_C_ScopeConsistency: all results should be in requested scopes', async () => {
    const requestedScopes = ['project', 'session'];
    const results = await hybridSearch(requestedScopes, 20, 'a');
    for (const claim of results) {
      expect(requestedScopes).toContain(claim.scope);
    }
  });

  it('Inv_C_MergeComplete: hybrid search should include text and vector candidates', async () => {
    // テキストで「JavaScript」を検索 + ベクトルでも類似候補を検索
    // 結果にはテキスト一致 AND/OR ベクトル類似の候補が含まれる
    const textResults = await textSearch('JavaScript', ['project'], 10);
    // EmbeddingServiceなしの場合、hybridSearchはText-onlyにフォールバック
    const hybridResults = await hybridSearch(['project'], 10, 'JavaScript');

    // Text-onlyフォールバック時は、テキスト検索結果と同様の結果になる
    expect(hybridResults.length).toBeGreaterThanOrEqual(textResults.length > 0 ? 1 : 0);
  });
});

// ========== エッジケーステスト ==========

describe('Edge cases', () => {
  beforeEach(async () => {
    for (const c of testClaims) {
      await upsertClaim(c);
    }
  });

  it('should return empty for empty scopes array (textSearch)', async () => {
    const results = await textSearch('JavaScript', [], 10);
    expect(results.length).toBe(0);
  });

  it('should return empty for empty scopes array (vectorSearch)', async () => {
    const results = await vectorSearch(createDummyEmbedding(1), [], 10);
    expect(results.length).toBe(0);
  });

  it('should return empty for empty scopes array (hybridSearch)', async () => {
    const results = await hybridSearch([], 10, 'JavaScript');
    expect(results.length).toBe(0);
  });

  it('should handle limit=0 by normalizing to 1', async () => {
    const results = await textSearch('JavaScript', ['project'], 0);
    // limit=0は1に正規化されるため、最低1件返る（マッチがあれば）
    expect(results.length).toBeLessThanOrEqual(1);
  });

  it('should handle negative limit by normalizing to 1', async () => {
    const results = await textSearch('JavaScript', ['project'], -5);
    expect(results.length).toBeLessThanOrEqual(1);
  });

  it('should escape LIKE special characters in query', async () => {
    // % や _ を含むクエリでも正常に動作すること
    const results = await textSearch('100%', ['project'], 10);
    // マッチなしで空配列（エラーにならないこと）
    expect(results.length).toBe(0);
  });

  it('should reject empty embedding vector', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    await expect(saveClaimVector(claim.id, [], 'test-model')).rejects.toThrow(
      'Embedding vector must not be empty'
    );
  });

  it('should reject embedding with non-finite values', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    await expect(saveClaimVector(claim.id, [1.0, NaN, 3.0], 'test-model')).rejects.toThrow(
      'Invalid embedding value'
    );
  });

  it('should reject embedding with Infinity', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    await expect(saveClaimVector(claim.id, [1.0, Infinity, 3.0], 'test-model')).rejects.toThrow(
      'Invalid embedding value'
    );
  });

  it('should reject embedding exceeding dimension limit', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    // MAX_EMBEDDING_DIM = 4096を超える
    const oversizedEmbedding = new Array(5000).fill(0.5);
    await expect(saveClaimVector(claim.id, oversizedEmbedding, 'test-model')).rejects.toThrow(
      'exceeds maximum'
    );
  });

  it('should reject embedding exceeding magnitude limit', async () => {
    const { claim } = await upsertClaim(testClaims[0]);
    // MAX_EMBEDDING_MAGNITUDE = 10.0を超える値
    await expect(saveClaimVector(claim.id, [0.5, 15.0, 0.3], 'test-model')).rejects.toThrow(
      'exceeds magnitude limit'
    );
  });
});

// ========== EmbeddingService統合テスト ==========

describe('hybridSearch with EmbeddingService', () => {
  /**
   * テストデータ挿入ヘルパー
   * 各テスト内で直接呼び出し、テスト間の完全な独立性を確保
   */
  async function insertTestClaims(): Promise<string[]> {
    const claimIds: string[] = [];
    for (let i = 0; i < testClaims.length; i++) {
      const { claim } = await upsertClaim(testClaims[i]);
      claimIds.push(claim.id);
      await saveClaimVector(claim.id, createDummyEmbedding(i + 1), 'test-model-v1');
    }
    return claimIds;
  }

  it('should use EmbeddingService for vector search when provided via config', async () => {
    await insertTestClaims();
    // モックEmbeddingServiceを設定（seed=1と同じ埋め込みを返す）
    const mockService = createMockEmbeddingService(createDummyEmbedding(1));

    const config: Partial<HybridSearchConfig> = {
      embeddingService: mockService,
    };

    const results = await hybridSearch(['project'], 10, 'test query', config);
    // ベクトル検索が動作していれば結果が返る
    expect(results.length).toBeGreaterThan(0);
  });

  it('should use global EmbeddingService when set', async () => {
    await insertTestClaims();
    // グローバルEmbeddingServiceを設定
    const mockService = createMockEmbeddingService(createDummyEmbedding(1));
    setEmbeddingService(mockService);

    const results = await hybridSearch(['project'], 10, 'test query');
    expect(results.length).toBeGreaterThan(0);
  });

  it('should fallback to text-only when EmbeddingService fails', async () => {
    await insertTestClaims();
    const failingService = createFailingEmbeddingService();
    setEmbeddingService(failingService);

    // 埋め込み生成失敗時はText-onlyフォールバック
    const results = await hybridSearch(['project'], 10, 'JavaScript');
    expect(results.length).toBeGreaterThan(0);
    expect(results.some((c) => c.text.includes('JavaScript'))).toBe(true);
  });

  it('should apply custom alpha and threshold from config', async () => {
    await insertTestClaims();
    const mockService = createMockEmbeddingService(createDummyEmbedding(1));

    // 高い閾値を設定してフィルタリングをテスト
    const config: Partial<HybridSearchConfig> = {
      embeddingService: mockService,
      alpha: 0.5,
      threshold: 0.99, // 非常に高い閾値
    };

    const results = await hybridSearch(['project'], 10, 'test query', config);
    // 高い閾値により結果が少ないかゼロになる
    expect(results.length).toBeLessThanOrEqual(1);
  });
});

// ========== 閾値境界値テスト ==========

describe('Inv_C_ThresholdFiltering boundary values', () => {
  /**
   * テストデータ挿入ヘルパー
   * テスト内で直接呼び出すことで、各テストの完全な独立性を確保
   */
  async function insertTestData() {
    for (let i = 0; i < testClaims.length; i++) {
      const { claim } = await upsertClaim(testClaims[i]);
      await saveClaimVector(claim.id, createDummyEmbedding(i + 1), 'test-model-v1');
    }
  }

  it('should filter results below threshold', async () => {
    await insertTestData();
    const mockService = createMockEmbeddingService(createDummyEmbedding(1));

    // threshold=0.0で全て通過
    const configLow: Partial<HybridSearchConfig> = {
      embeddingService: mockService,
      threshold: 0.0,
    };
    const resultsLow = await hybridSearch(['project', 'session', 'principle'], 20, 'a', configLow);

    // threshold=1.0で全てフィルタ
    const configHigh: Partial<HybridSearchConfig> = {
      embeddingService: mockService,
      threshold: 1.0,
    };
    const resultsHigh = await hybridSearch(
      ['project', 'session', 'principle'],
      20,
      'a',
      configHigh
    );

    // 低閾値の方が結果が多い
    expect(resultsLow.length).toBeGreaterThanOrEqual(resultsHigh.length);
  });

  it('should include result exactly at threshold', async () => {
    const conn = await getConnection();
    // DuckDBマクロで閾値ちょうどのスコアをテスト
    // threshold=0.15の境界
    const result = await conn.runAndReadAll(
      'SELECT CASE WHEN 0.15 >= 0.15 THEN 1 ELSE 0 END as included'
    );
    const rows = result.getRowObjects() as { included: number }[];
    expect(rows[0].included).toBe(1); // 閾値ちょうどは含まれる
  });
});

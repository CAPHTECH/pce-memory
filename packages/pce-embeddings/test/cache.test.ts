/**
 * EmbeddingCache テスト
 * TLA+ Inv_CacheVersionConsistency準拠
 *
 * テスト対象:
 * 1. キャッシュ基本操作（get/set）
 * 2. TTL有効期限
 * 3. モデルバージョン整合性
 * 4. バージョン指定無効化
 * 5. 最大エントリ数制限
 */
import { describe, it, expect } from "vitest";
import * as E from "fp-ts/Either";
import {
  createInMemoryCache,
  getCacheStats,
  createTestCache,
} from "../src/cache.js";

// ========== 基本操作テスト ==========

describe("InMemoryCache - Basic Operations", () => {
  it("should return undefined for non-existent key", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    const result = await cache.get("nonexistent-hash")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it("should store and retrieve embedding", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });
    const embedding = [0.1, 0.2, 0.3];

    await cache.set("test-hash", embedding, "v1")();
    const result = await cache.get("test-hash")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeDefined();
      expect(result.right!.embedding).toEqual(embedding);
      expect(result.right!.modelVersion).toBe("v1");
    }
  });

  it("should invalidate all entries", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    await cache.set("hash1", [1, 2, 3], "v1")();
    await cache.set("hash2", [4, 5, 6], "v1")();

    await cache.invalidateAll()();

    const result1 = await cache.get("hash1")();
    const result2 = await cache.get("hash2")();

    expect(E.isRight(result1) && result1.right).toBeUndefined();
    expect(E.isRight(result2) && result2.right).toBeUndefined();
  });
});

// ========== バージョン整合性テスト ==========

describe("InMemoryCache - Version Consistency", () => {
  it("should include model version in cache entry", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "model-v1" });

    await cache.set("test-hash", [0.1, 0.2], "model-v1")();
    const result = await cache.get("test-hash")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result) && result.right) {
      expect(result.right.modelVersion).toBe("model-v1");
    }
  });

  it("should not return entry after model version update", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    // v1で保存
    await cache.set("test-hash", [0.1, 0.2], "v1")();

    // バージョン更新
    await cache.updateModelVersion("v2")();

    // v2で検索（見つからないはず）
    const result = await cache.get("test-hash")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it("should clear cache on model version update", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    await cache.set("hash1", [1], "v1")();
    await cache.set("hash2", [2], "v1")();

    // 更新前の統計
    const statsBefore = getCacheStats(cache);
    expect(statsBefore.entryCount).toBe(2);

    // バージョン更新
    await cache.updateModelVersion("v2")();

    // 更新後の統計
    const statsAfter = getCacheStats(cache);
    expect(statsAfter.entryCount).toBe(0);
    expect(statsAfter.modelVersion).toBe("v2");
  });

  it("should not clear cache when updating to same version", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    await cache.set("test-hash", [1, 2, 3], "v1")();

    // 同じバージョンに更新
    await cache.updateModelVersion("v1")();

    // まだ存在するはず
    const result = await cache.get("test-hash")();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeDefined();
    }
  });
});

// ========== バージョン指定無効化テスト ==========

describe("InMemoryCache - invalidateByModelVersion", () => {
  it("should invalidate only specified version entries", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    // v1で保存
    await cache.set("hash-v1", [1, 2, 3], "v1")();

    // v2に更新して保存
    await cache.updateModelVersion("v2")();
    await cache.set("hash-v2", [4, 5, 6], "v2")();

    // v1のエントリを無効化（ただしすでにv2に更新されているので影響なし）
    // 実際のユースケースでは古いバージョンのキャッシュを削除するために使用
    await cache.invalidateByModelVersion("v1")();

    // v2のエントリは残る
    const result = await cache.get("hash-v2")();
    expect(E.isRight(result) && result.right?.embedding).toEqual([4, 5, 6]);
  });
});

// ========== TTLテスト ==========

describe("InMemoryCache - TTL", () => {
  it("should expire entry after TTL", async () => {
    const cache = createInMemoryCache({
      initialModelVersion: "v1",
      ttlMs: 100, // 100ms TTL
    });

    await cache.set("test-hash", [1, 2, 3], "v1")();

    // TTL前は取得可能
    const resultBefore = await cache.get("test-hash")();
    expect(E.isRight(resultBefore) && resultBefore.right).toBeDefined();

    // TTL経過を待つ
    await new Promise((resolve) => setTimeout(resolve, 150));

    // TTL後は取得不可
    const resultAfter = await cache.get("test-hash")();
    expect(E.isRight(resultAfter) && resultAfter.right).toBeUndefined();
  });
});

// ========== 最大エントリ数テスト ==========

describe("InMemoryCache - Max Entries", () => {
  it("should evict old entries when max entries exceeded", async () => {
    const cache = createInMemoryCache({
      initialModelVersion: "v1",
      maxEntries: 3,
    });

    // 4つのエントリを追加（maxは3）
    await cache.set("hash1", [1], "v1")();
    await new Promise((r) => setTimeout(r, 10)); // createdAt差をつける
    await cache.set("hash2", [2], "v1")();
    await new Promise((r) => setTimeout(r, 10));
    await cache.set("hash3", [3], "v1")();
    await new Promise((r) => setTimeout(r, 10));
    await cache.set("hash4", [4], "v1")();

    // 最も古いhash1が削除されているはず
    const stats = getCacheStats(cache);
    expect(stats.entryCount).toBeLessThanOrEqual(3);

    // 新しいエントリは残っている
    const result4 = await cache.get("hash4")();
    expect(E.isRight(result4) && result4.right).toBeDefined();
  });
});

// ========== 統計情報テスト ==========

describe("InMemoryCache - getCacheStats", () => {
  it("should return correct stats for empty cache", () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    const stats = getCacheStats(cache);

    expect(stats.entryCount).toBe(0);
    expect(stats.modelVersion).toBe("v1");
    expect(stats.oldestEntryAt).toBeUndefined();
    expect(stats.newestEntryAt).toBeUndefined();
  });

  it("should return correct stats for populated cache", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    await cache.set("hash1", [1], "v1")();
    await new Promise((r) => setTimeout(r, 10));
    await cache.set("hash2", [2], "v1")();

    const stats = getCacheStats(cache);

    expect(stats.entryCount).toBe(2);
    expect(stats.modelVersion).toBe("v1");
    expect(stats.oldestEntryAt).toBeDefined();
    expect(stats.newestEntryAt).toBeDefined();
    expect(stats.oldestEntryAt).toBeLessThan(stats.newestEntryAt!);
  });
});

// ========== ファクトリ関数テスト ==========

describe("InMemoryCache - Factory Functions", () => {
  it("should create test cache with default version", () => {
    const cache = createTestCache();

    expect(cache.currentModelVersion).toBe("test-v1");
  });

  it("should create test cache with custom version", () => {
    const cache = createTestCache("custom-version");

    expect(cache.currentModelVersion).toBe("custom-version");
  });
});

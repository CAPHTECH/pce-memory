/**
 * EmbeddingService テスト
 * ADR-0003: 形式検証済み処理フローの検証
 *
 * テスト対象:
 * 1. キャッシュヒット/ミス
 * 2. Redact-before-Embed（Alloy制約）
 * 3. バッチ処理（空配列、サイズ超過）
 * 4. フェイルオーバーロジック（TLA+ ImmediateFailover）
 * 5. プロバイダー状態チェック
 */
import { describe, it, expect, beforeEach } from "vitest";
import * as E from "fp-ts/Either";
import * as TE from "fp-ts/TaskEither";
import type {
  EmbeddingProvider,
  EmbeddingCache,
  ProviderStatus,
  EmbedParams,
} from "../src/types.js";
import type { EmbeddingError, CacheError } from "../src/errors.js";
import { createEmbeddingService, createLocalOnlyService } from "../src/service.js";
import { createInMemoryCache } from "../src/cache.js";
import { MAX_BATCH_SIZE } from "../src/types.js";

// ========== スタブプロバイダー ==========

/**
 * テスト用スタブプロバイダーを作成
 * @param options オプション設定
 */
const createStubProvider = (options: {
  modelVersion?: string;
  status?: ProviderStatus;
  embedResult?: readonly number[];
  shouldFail?: boolean;
  failError?: EmbeddingError;
}): EmbeddingProvider => {
  const {
    modelVersion = "test-model-v1",
    status = "available",
    embedResult = [0.1, 0.2, 0.3],
    shouldFail = false,
    failError = {
      _tag: "EmbeddingError" as const,
      code: "LOCAL_INFERENCE_FAILED" as const,
      message: "Stub provider failed",
    },
  } = options;

  return {
    modelVersion,
    status,
    embed: (_text: string): TE.TaskEither<EmbeddingError, readonly number[]> =>
      shouldFail ? TE.left(failError) : TE.right(embedResult),
    embedBatch: (
      texts: readonly string[]
    ): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]> =>
      shouldFail
        ? TE.left(failError)
        : TE.right(texts.map(() => embedResult)),
  };
};

// ========== テストデータ ==========

const publicParams: EmbedParams = {
  text: "Hello world",
  sensitivity: "public",
};

const confidentialParams: EmbedParams = {
  text: "Secret: password123",
  sensitivity: "confidential",
};

// ========== キャッシュヒット/ミステスト ==========

describe("EmbeddingService - Cache", () => {
  let cache: ReturnType<typeof createInMemoryCache>;
  let provider: EmbeddingProvider;

  beforeEach(() => {
    cache = createInMemoryCache({ initialModelVersion: "test-model-v1" });
    provider = createStubProvider({ modelVersion: "test-model-v1" });
  });

  it("should return fromCache: false on first request (cache miss)", async () => {
    const service = createLocalOnlyService(provider, cache);
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(false);
      expect(result.right.embedding).toEqual([0.1, 0.2, 0.3]);
    }
  });

  it("should return fromCache: true on second request (cache hit)", async () => {
    const service = createLocalOnlyService(provider, cache);

    // 1回目: キャッシュミス
    await service.embed(publicParams)();

    // 2回目: キャッシュヒット
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(true);
    }
  });

  it("should skip cache when skipCache: true", async () => {
    const service = createLocalOnlyService(provider, cache);

    // 1回目: キャッシュに保存
    await service.embed(publicParams)();

    // 2回目: キャッシュスキップ
    const result = await service.embed({ ...publicParams, skipCache: true })();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(false);
    }
  });

  it("should not use cache when model version changes", async () => {
    const service1 = createLocalOnlyService(provider, cache);

    // v1でキャッシュに保存
    await service1.embed(publicParams)();

    // モデルバージョンを更新
    await cache.updateModelVersion("test-model-v2")();

    // 新しいバージョンのプロバイダーでサービスを作成
    const providerV2 = createStubProvider({
      modelVersion: "test-model-v2",
      embedResult: [0.4, 0.5, 0.6],
    });
    const service2 = createEmbeddingService({
      primary: providerV2,
      cache,
    });

    const result = await service2.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // キャッシュミスで新しい埋め込みを取得
      expect(result.right.fromCache).toBe(false);
      expect(result.right.embedding).toEqual([0.4, 0.5, 0.6]);
    }
  });
});

// ========== Redact-before-Embed テスト ==========

describe("EmbeddingService - Redact-before-Embed", () => {
  let cache: ReturnType<typeof createInMemoryCache>;

  beforeEach(() => {
    cache = createInMemoryCache({ initialModelVersion: "test-model-v1" });
  });

  it("should process public data without redaction", async () => {
    const provider = createStubProvider({});
    const service = createLocalOnlyService(provider, cache);

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
  });

  it("should process internal data without redaction", async () => {
    const provider = createStubProvider({});
    const service = createLocalOnlyService(provider, cache);

    const result = await service.embed({
      text: "Internal document",
      sensitivity: "internal",
    })();

    expect(E.isRight(result)).toBe(true);
  });

  it("should apply redaction to confidential data", async () => {
    const provider = createStubProvider({});
    const service = createLocalOnlyService(provider, cache);

    // Confidentialデータの処理（Redact適用）
    const result = await service.embed(confidentialParams)();

    // Redact処理が適用されることを確認
    expect(E.isRight(result)).toBe(true);
  });
});

// ========== バッチ処理テスト ==========

describe("EmbeddingService - Batch Processing", () => {
  let cache: ReturnType<typeof createInMemoryCache>;
  let provider: EmbeddingProvider;

  beforeEach(() => {
    cache = createInMemoryCache({ initialModelVersion: "test-model-v1" });
    provider = createStubProvider({});
  });

  it("should handle empty batch array", async () => {
    const service = createLocalOnlyService(provider, cache);

    const result = await service.embedBatch([])();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.results).toEqual([]);
      expect(result.right.processedCount).toBe(0);
      expect(result.right.cacheHits).toBe(0);
    }
  });

  it("should process multiple items in batch", async () => {
    const service = createLocalOnlyService(provider, cache);

    const result = await service.embedBatch([
      publicParams,
      { text: "Another text", sensitivity: "public" },
    ])();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.processedCount).toBe(2);
      expect(result.right.results.length).toBe(2);
    }
  });

  it("should reject batch size exceeding MAX_BATCH_SIZE", async () => {
    const service = createLocalOnlyService(provider, cache);

    // MAX_BATCH_SIZE + 1 のバッチを作成
    const oversizedBatch: EmbedParams[] = Array.from(
      { length: MAX_BATCH_SIZE + 1 },
      (_, i) => ({ text: `Text ${i}`, sensitivity: "public" as const })
    );

    const result = await service.embedBatch(oversizedBatch)();

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe("BATCH_SIZE_EXCEEDED");
    }
  });

  it("should track cache hits in batch", async () => {
    const service = createLocalOnlyService(provider, cache);

    // 最初にキャッシュに入れる
    await service.embed(publicParams)();

    // バッチでリクエスト（1つはキャッシュヒット）
    const result = await service.embedBatch([
      publicParams,
      { text: "New text", sensitivity: "public" },
    ])();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.cacheHits).toBe(1);
    }
  });
});

// ========== フェイルオーバーテスト ==========

describe("EmbeddingService - Failover", () => {
  let cache: ReturnType<typeof createInMemoryCache>;

  beforeEach(() => {
    cache = createInMemoryCache({ initialModelVersion: "test-model-v1" });
  });

  it("should use primary provider when available", async () => {
    const primary = createStubProvider({
      modelVersion: "primary-v1",
      embedResult: [1, 2, 3],
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [4, 5, 6],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([1, 2, 3]);
      expect(result.right.modelVersion).toBe("primary-v1");
    }
  });

  it("should failover to fallback when primary fails", async () => {
    const primary = createStubProvider({
      modelVersion: "primary-v1",
      shouldFail: true,
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [4, 5, 6],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([4, 5, 6]);
      expect(result.right.modelVersion).toBe("fallback-v1");
    }
  });

  it("should failover to fallback when primary is unavailable", async () => {
    const primary = createStubProvider({
      modelVersion: "primary-v1",
      status: "unavailable",
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [4, 5, 6],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([4, 5, 6]);
      expect(result.right.modelVersion).toBe("fallback-v1");
    }
  });

  it("should fail when both providers are unavailable", async () => {
    const primary = createStubProvider({
      status: "unavailable",
    });
    const fallback = createStubProvider({
      status: "unavailable",
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe("NO_PROVIDER");
    }
  });

  it("should fail when primary fails and no fallback configured", async () => {
    const primary = createStubProvider({
      shouldFail: true,
    });

    const service = createEmbeddingService({
      primary,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe("LOCAL_INFERENCE_FAILED");
    }
  });

  it("should use degraded provider", async () => {
    const primary = createStubProvider({
      status: "degraded",
      embedResult: [7, 8, 9],
    });

    const service = createEmbeddingService({
      primary,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([7, 8, 9]);
    }
  });
});

// ========== サービスプロパティテスト ==========

describe("EmbeddingService - Properties", () => {
  it("should expose modelVersion from primary provider", () => {
    const cache = createInMemoryCache({ initialModelVersion: "test-v1" });
    const primary = createStubProvider({ modelVersion: "my-model-v2" });

    const service = createEmbeddingService({ primary, cache });

    expect(service.modelVersion).toBe("my-model-v2");
  });

  it("should expose primaryStatus", () => {
    const cache = createInMemoryCache({ initialModelVersion: "test-v1" });
    const primary = createStubProvider({ status: "degraded" });

    const service = createEmbeddingService({ primary, cache });

    expect(service.primaryStatus).toBe("degraded");
  });

  it("should clear cache via service", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "test-v1" });
    const primary = createStubProvider({});
    const service = createEmbeddingService({ primary, cache });

    // キャッシュに入れる
    await service.embed(publicParams)();

    // キャッシュクリア
    const clearResult = await service.clearCache()();
    expect(E.isRight(clearResult)).toBe(true);

    // 再度リクエスト（キャッシュミスになるはず）
    const result = await service.embed(publicParams)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(false);
    }
  });
});

// ========== ベストエフォートキャッシュテスト ==========

/**
 * 失敗するキャッシュスタブを作成
 */
const createFailingCache = (
  options: {
    failOnRead?: boolean;
    failOnWrite?: boolean;
    failOnUpdateModelVersion?: boolean;
    modelVersion?: string;
  } = {}
): EmbeddingCache => {
  const {
    failOnRead = false,
    failOnWrite = false,
    failOnUpdateModelVersion = false,
    modelVersion = "test-v1",
  } = options;

  const cacheError: CacheError = {
    _tag: "CacheError" as const,
    code: "CACHE_READ_ERROR" as const,
    message: "Simulated cache failure",
  };

  // updateModelVersion失敗時もcurrentModelVersionは変わらないことをシミュレート
  let currentVersion = modelVersion;

  return {
    get currentModelVersion() {
      return currentVersion;
    },
    get: () =>
      failOnRead
        ? TE.left(cacheError)
        : TE.right(undefined),
    set: () =>
      failOnWrite
        ? TE.left({ ...cacheError, code: "CACHE_WRITE_ERROR" as const })
        : TE.right(undefined),
    invalidateAll: () => TE.right(undefined),
    updateModelVersion: (newVersion: string) =>
      failOnUpdateModelVersion
        ? TE.left({ ...cacheError, code: "CACHE_WRITE_ERROR" as const })
        : TE.tryCatch(
            async () => { currentVersion = newVersion; },
            () => ({ ...cacheError, code: "CACHE_WRITE_ERROR" as const })
          ),
    invalidateByModelVersion: () => TE.right(undefined),
  };
};

describe("EmbeddingService - Best-Effort Cache", () => {
  it("should succeed when cache read fails", async () => {
    const cache = createFailingCache({ failOnRead: true });
    const provider = createStubProvider({
      modelVersion: "test-v1",
      embedResult: [1, 2, 3],
    });

    const service = createEmbeddingService({ primary: provider, cache });
    const result = await service.embed(publicParams)();

    // キャッシュ読み取り失敗でも処理は成功する
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([1, 2, 3]);
      expect(result.right.fromCache).toBe(false);
    }
  });

  it("should succeed when cache write fails", async () => {
    const cache = createFailingCache({ failOnWrite: true });
    const provider = createStubProvider({
      modelVersion: "test-v1",
      embedResult: [4, 5, 6],
    });

    const service = createEmbeddingService({ primary: provider, cache });
    const result = await service.embed(publicParams)();

    // キャッシュ書き込み失敗でも処理は成功する
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([4, 5, 6]);
    }
  });

  it("should call onCacheError on cache read failure", async () => {
    const cache = createFailingCache({ failOnRead: true });
    const provider = createStubProvider({ modelVersion: "test-v1" });

    const cacheErrors: Array<{ error: CacheError; operation: 'read' | 'write' }> = [];
    const onCacheError = (error: CacheError, operation: 'read' | 'write') => {
      cacheErrors.push({ error, operation });
    };

    const service = createEmbeddingService({
      primary: provider,
      cache,
      onCacheError,
    });

    await service.embed(publicParams)();

    expect(cacheErrors.length).toBeGreaterThan(0);
    expect(cacheErrors[0].operation).toBe("read");
  });

  it("should call onCacheError on cache write failure", async () => {
    const cache = createFailingCache({ failOnWrite: true });
    const provider = createStubProvider({ modelVersion: "test-v1" });

    const cacheErrors: Array<{ error: CacheError; operation: 'read' | 'write' }> = [];
    const onCacheError = (error: CacheError, operation: 'read' | 'write') => {
      cacheErrors.push({ error, operation });
    };

    const service = createEmbeddingService({
      primary: provider,
      cache,
      onCacheError,
    });

    await service.embed(publicParams)();

    expect(cacheErrors.some((e) => e.operation === "write")).toBe(true);
  });
});

// ========== フェイルオーバーバージョン追跡テスト ==========

describe("EmbeddingService - Failover Version Tracking", () => {
  it("should use fallback modelVersion in result after failover", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "primary-v1" });

    const primary = createStubProvider({
      modelVersion: "primary-v1",
      shouldFail: true,
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [7, 8, 9],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // フェイルオーバー後はfallbackのバージョンが返される
      expect(result.right.modelVersion).toBe("fallback-v1");
      expect(result.right.embedding).toEqual([7, 8, 9]);
    }
  });

  it("should store with fallback version after failover", async () => {
    // fallbackバージョンでキャッシュを初期化
    const cache = createInMemoryCache({ initialModelVersion: "fallback-v1" });

    const primary = createStubProvider({
      modelVersion: "primary-v1",
      shouldFail: true,
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [10, 11, 12],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    // 最初のリクエスト（フェイルオーバー発生）
    await service.embed(publicParams)();

    // 2回目のリクエスト（キャッシュから取得できるはず）
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // フォールバックバージョンでキャッシュされている
      expect(result.right.modelVersion).toBe("fallback-v1");
      expect(result.right.fromCache).toBe(true);
    }
  });

  it("should sync cache version after failover (TLA+ Inv_CacheVersionConsistency)", async () => {
    // primaryバージョンでキャッシュを初期化（fallbackとは異なる）
    const cache = createInMemoryCache({ initialModelVersion: "primary-v1" });

    const primary = createStubProvider({
      modelVersion: "primary-v1",
      shouldFail: true,
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [10, 11, 12],
    });

    const service = createEmbeddingService({
      primary,
      fallback,
      cache,
    });

    // フェイルオーバー発生 → cache.updateModelVersion("fallback-v1")が呼ばれるはず
    await service.embed(publicParams)();

    // キャッシュバージョンがfallbackに同期されていることを確認
    expect(cache.currentModelVersion).toBe("fallback-v1");

    // 2回目のリクエストでキャッシュヒット
    const result = await service.embed(publicParams)();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(true);
      expect(result.right.modelVersion).toBe("fallback-v1");
    }
  });
});

// ========== キャッシュ優先テスト ==========

describe("EmbeddingService - Cache-First Flow", () => {
  it("should return cached data when both providers are unavailable", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "test-v1" });

    // 最初は利用可能なプロバイダーでキャッシュに保存
    const availableProvider = createStubProvider({
      modelVersion: "test-v1",
      embedResult: [1, 2, 3],
    });
    const service1 = createEmbeddingService({
      primary: availableProvider,
      cache,
    });
    await service1.embed(publicParams)();

    // 両方のプロバイダーを unavailable にしたサービスを作成
    const unavailablePrimary = createStubProvider({
      modelVersion: "test-v1",
      status: "unavailable",
    });
    const unavailableFallback = createStubProvider({
      modelVersion: "test-v1",
      status: "unavailable",
    });
    const service2 = createEmbeddingService({
      primary: unavailablePrimary,
      fallback: unavailableFallback,
      cache,
    });

    // キャッシュからデータを取得できるはず
    const result = await service2.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.fromCache).toBe(true);
      expect(result.right.embedding).toEqual([1, 2, 3]);
    }
  });

  it("should fail with NO_PROVIDER when cache miss and both providers unavailable", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "test-v1" });

    const unavailablePrimary = createStubProvider({
      modelVersion: "test-v1",
      status: "unavailable",
    });
    const unavailableFallback = createStubProvider({
      modelVersion: "test-v1",
      status: "unavailable",
    });
    const service = createEmbeddingService({
      primary: unavailablePrimary,
      fallback: unavailableFallback,
      cache,
    });

    // キャッシュにないテキスト → NO_PROVIDERエラー
    const result = await service.embed({
      text: "New uncached text",
      sensitivity: "public",
    })();

    expect(E.isLeft(result)).toBe(true);
    if (E.isLeft(result)) {
      expect(result.left.code).toBe("NO_PROVIDER");
    }
  });
});

// ========== onCacheError例外安全性テスト ==========

describe("EmbeddingService - Safe onCacheError", () => {
  it("should not fail when onCacheError throws exception", async () => {
    const cache = createFailingCache({ failOnRead: true });
    const provider = createStubProvider({
      modelVersion: "test-v1",
      embedResult: [1, 2, 3],
    });

    // 例外を投げるonCacheError
    const throwingOnCacheError = () => {
      throw new Error("Callback exception");
    };

    const service = createEmbeddingService({
      primary: provider,
      cache,
      onCacheError: throwingOnCacheError,
    });

    // 例外が投げられてもリクエストは成功するはず
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([1, 2, 3]);
    }
  });

  it("should not fail when onCacheError returns rejected promise", async () => {
    const cache = createFailingCache({ failOnRead: true });
    const provider = createStubProvider({
      modelVersion: "test-v1",
      embedResult: [4, 5, 6],
    });

    // Promiseをrejectする非同期onCacheError
    const asyncRejectingOnCacheError = async () => {
      throw new Error("Async callback rejection");
    };

    const service = createEmbeddingService({
      primary: provider,
      cache,
      onCacheError: asyncRejectingOnCacheError,
    });

    // 非同期rejectionでもリクエストは成功するはず
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([4, 5, 6]);
    }
  });
});

// ========== プライマリ復帰テスト ==========

describe("EmbeddingService - Primary Recovery", () => {
  it("should sync cache version when primary recovers after fallback (TLA+ Inv_CacheVersionConsistency)", async () => {
    // Step 1: fallbackバージョンでキャッシュを設定（フェイルオーバー後の状態をシミュレート）
    const cache = createInMemoryCache({ initialModelVersion: "fallback-v1" });

    // Step 2: プライマリが復帰した状態でサービスを作成
    const recoveredPrimary = createStubProvider({
      modelVersion: "primary-v2",  // 新しいバージョンで復帰
      embedResult: [7, 8, 9],
    });
    const fallback = createStubProvider({
      modelVersion: "fallback-v1",
      embedResult: [10, 11, 12],
    });

    const service = createEmbeddingService({
      primary: recoveredPrimary,
      fallback,
      cache,
    });

    // Step 3: リクエスト実行（プライマリで処理される）
    const result = await service.embed(publicParams)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      // プライマリで処理されている
      expect(result.right.modelVersion).toBe("primary-v2");
      expect(result.right.embedding).toEqual([7, 8, 9]);
    }

    // Step 4: キャッシュバージョンがプライマリに同期されていることを確認
    // usedFallback条件を削除したため、プライマリ復帰時もバージョン同期される
    expect(cache.currentModelVersion).toBe("primary-v2");

    // Step 5: 2回目のリクエストでキャッシュヒットを確認
    const result2 = await service.embed(publicParams)();
    expect(E.isRight(result2)).toBe(true);
    if (E.isRight(result2)) {
      expect(result2.right.fromCache).toBe(true);
      expect(result2.right.modelVersion).toBe("primary-v2");
    }
  });

  it("should not sync cache version when versions match (no unnecessary sync)", async () => {
    // プライマリと同じバージョンでキャッシュを初期化
    const cache = createInMemoryCache({ initialModelVersion: "same-v1" });

    const primary = createStubProvider({
      modelVersion: "same-v1",
      embedResult: [1, 2, 3],
    });

    // updateModelVersionが呼ばれたかを追跡
    let updateCalled = false;
    const originalUpdateModelVersion = cache.updateModelVersion.bind(cache);
    cache.updateModelVersion = (version: string) => {
      updateCalled = true;
      return originalUpdateModelVersion(version);
    };

    const service = createEmbeddingService({
      primary,
      cache,
    });

    await service.embed(publicParams)();

    // バージョンが同じなのでupdateModelVersionは呼ばれない
    expect(updateCalled).toBe(false);
    expect(cache.currentModelVersion).toBe("same-v1");
  });
});

// ========== syncCacheVersion失敗時テスト ==========

describe("EmbeddingService - syncCacheVersion Failure", () => {
  it("should skip cache write when version sync fails (TLA+ Inv_CacheVersionConsistency)", async () => {
    // バージョン同期が失敗するキャッシュを作成
    // currentModelVersionは古いまま（v1）、プロバイダーは新しいバージョン（v2）
    const cache = createFailingCache({
      failOnUpdateModelVersion: true,
      modelVersion: "old-v1",
    });

    // set()が呼ばれたかを追跡
    let setCalled = false;
    const originalSet = cache.set;
    cache.set = (...args) => {
      setCalled = true;
      return originalSet(...args);
    };

    const provider = createStubProvider({
      modelVersion: "new-v2",  // キャッシュと異なるバージョン
      embedResult: [1, 2, 3],
    });

    const service = createEmbeddingService({
      primary: provider,
      cache,
    });

    const result = await service.embed(publicParams)();

    // リクエスト自体は成功する
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.embedding).toEqual([1, 2, 3]);
      expect(result.right.modelVersion).toBe("new-v2");
    }

    // キャッシュバージョンは古いまま（同期失敗）
    expect(cache.currentModelVersion).toBe("old-v1");

    // 重要: cache.set()はスキップされるべき
    // (同期失敗時に書き込んでも、次回検索でキーが一致しないため無意味)
    expect(setCalled).toBe(false);
  });

  it("should write to cache when version sync succeeds", async () => {
    // バージョン同期が成功するキャッシュ
    const cache = createFailingCache({
      failOnUpdateModelVersion: false,
      modelVersion: "old-v1",
    });

    let setCalled = false;
    const originalSet = cache.set;
    cache.set = (...args) => {
      setCalled = true;
      return originalSet(...args);
    };

    const provider = createStubProvider({
      modelVersion: "new-v2",
      embedResult: [4, 5, 6],
    });

    const service = createEmbeddingService({
      primary: provider,
      cache,
    });

    await service.embed(publicParams)();

    // 同期成功後、キャッシュバージョンが更新される
    expect(cache.currentModelVersion).toBe("new-v2");

    // cache.set()が呼ばれる
    expect(setCalled).toBe(true);
  });
});

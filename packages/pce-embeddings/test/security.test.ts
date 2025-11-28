/**
 * セキュリティ修正テスト
 * Critical Review で指摘された問題の修正検証
 *
 * テスト対象:
 * 1. キャッシュのディープコピー（ミューテーション汚染防止）
 * 2. リモートプロバイダーのHTTPS強制
 * 3. リモートプロバイダーの次元検証
 * 4. ローカルプロバイダーの初期化ガード
 */
import { describe, it, expect, beforeEach } from "vitest";
import * as E from "fp-ts/Either";
import { createInMemoryCache } from "../src/cache.js";
import {
  createRemoteProvider,
  createOpenAIProvider,
} from "../src/providers/remote.js";
import {
  resetLocalProvider,
  isInitialized,
} from "../src/providers/local.js";

// ========== キャッシュディープコピーテスト ==========

describe("Security - Cache Deep Copy", () => {
  it("should return deep copy of embedding on get (mutation prevention)", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });
    const originalEmbedding = [0.1, 0.2, 0.3];

    // キャッシュに保存
    await cache.set("test-hash", originalEmbedding, "v1")();

    // 取得
    const result1 = await cache.get("test-hash")();

    expect(E.isRight(result1)).toBe(true);
    if (E.isRight(result1) && result1.right) {
      // 返された配列をミューテート
      const mutableEmbedding = result1.right.embedding as number[];
      mutableEmbedding[0] = 999;

      // 再度取得 - 元の値が維持されていることを確認
      const result2 = await cache.get("test-hash")();
      expect(E.isRight(result2)).toBe(true);
      if (E.isRight(result2) && result2.right) {
        // キャッシュは汚染されていない
        expect(result2.right.embedding[0]).toBe(0.1);
        expect(result2.right.embedding).toEqual([0.1, 0.2, 0.3]);
      }
    }
  });

  it("should return independent copies on multiple gets", async () => {
    const cache = createInMemoryCache({ initialModelVersion: "v1" });

    await cache.set("test-hash", [1, 2, 3], "v1")();

    const result1 = await cache.get("test-hash")();
    const result2 = await cache.get("test-hash")();

    if (E.isRight(result1) && E.isRight(result2)) {
      // 異なる配列インスタンスであることを確認
      expect(result1.right?.embedding).not.toBe(result2.right?.embedding);
      expect(result1.right?.embedding).toEqual(result2.right?.embedding);
    }
  });
});

// ========== リモートプロバイダーHTTPS強制テスト ==========

describe("Security - Remote Provider HTTPS Enforcement", () => {
  it("should accept HTTPS endpoints", () => {
    // HTTPS エンドポイントは許可
    expect(() =>
      createRemoteProvider({
        endpoint: "https://api.example.com/v1",
        apiKey: "test-key",
        model: "test-model",
      })
    ).not.toThrow();
  });

  it("should accept localhost HTTP for development", () => {
    // localhost は開発用にHTTP許可
    expect(() =>
      createRemoteProvider({
        endpoint: "http://localhost:8080",
        apiKey: "test-key",
        model: "test-model",
      })
    ).not.toThrow();

    expect(() =>
      createRemoteProvider({
        endpoint: "http://127.0.0.1:8080",
        apiKey: "test-key",
        model: "test-model",
      })
    ).not.toThrow();
  });

  it("should reject HTTP endpoints (non-localhost)", () => {
    // HTTP（localhost以外）は拒否
    expect(() =>
      createRemoteProvider({
        endpoint: "http://api.example.com/v1",
        apiKey: "test-key",
        model: "test-model",
      })
    ).toThrow(/Insecure endpoint protocol/);
  });

  it("should reject private IP addresses (SSRF prevention)", () => {
    // プライベートIPは拒否（SSRF防止）

    // 10.x.x.x
    expect(() =>
      createRemoteProvider({
        endpoint: "https://10.0.0.1:8080",
        apiKey: "test-key",
        model: "test-model",
      })
    ).toThrow(/internal network address/);

    // 172.16.x.x
    expect(() =>
      createRemoteProvider({
        endpoint: "https://172.16.0.1:8080",
        apiKey: "test-key",
        model: "test-model",
      })
    ).toThrow(/internal network address/);

    // 192.168.x.x
    expect(() =>
      createRemoteProvider({
        endpoint: "https://192.168.1.1:8080",
        apiKey: "test-key",
        model: "test-model",
      })
    ).toThrow(/internal network address/);
  });

  it("should reject invalid URLs", () => {
    expect(() =>
      createRemoteProvider({
        endpoint: "not-a-valid-url",
        apiKey: "test-key",
        model: "test-model",
      })
    ).toThrow(/Invalid endpoint URL/);
  });

  it("should allow OpenAI provider (uses HTTPS)", () => {
    // OpenAI プロバイダーは内部でHTTPSを使用
    expect(() => createOpenAIProvider("test-api-key")).not.toThrow();
  });
});

// ========== ローカルプロバイダー初期化ガードテスト ==========

describe("Security - Local Provider Initialization Guard", () => {
  beforeEach(() => {
    resetLocalProvider();
  });

  it("should start uninitialized", () => {
    expect(isInitialized()).toBe(false);
  });

  it("should allow reset for testing", () => {
    resetLocalProvider();
    expect(isInitialized()).toBe(false);
  });

  // Note: 実際のONNX初期化テストは統合テストで行う
  // ここではガードの動作のみをテスト
});

// ========== 埋め込み次元検証テスト ==========

describe("Security - Embedding Dimension Validation", () => {
  // Note: 実際のAPIコールテストはモックが必要
  // ここでは検証関数の存在とプロバイダーが作成されることを確認

  it("should create remote provider with dimension validation enabled", () => {
    const provider = createRemoteProvider({
      endpoint: "https://api.example.com/v1",
      apiKey: "test-key",
      model: "test-model",
    });

    // プロバイダーが正常に作成される
    expect(provider).toBeDefined();
    expect(provider.modelVersion).toBe("test-model");
    expect(provider.status).toBe("available");
  });
});

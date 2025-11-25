/**
 * ポリシーストアのテスト
 * ADR-0002: ポリシー永続化機能の検証
 */
import { describe, it, expect, beforeEach } from "vitest";
import { initDb, initSchema, resetDb } from "../src/db/connection";
import { savePolicy, loadLatestPolicy, loadPolicyByVersion, hasStoredPolicy } from "../src/store/policy";
import { defaultPolicy } from "@pce/policy-schemas/src/defaults";
import * as E from "fp-ts/Either";

beforeEach(async () => {
  resetDb();
  process.env.PCE_DB = ":memory:";
  await initDb();
  await initSchema();
});

describe("savePolicy", () => {
  it("saves policy and returns id and version", async () => {
    const result = await savePolicy("1.0", "version: 1.0", defaultPolicy.boundary)();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right.id).toMatch(/^pol_/);
      expect(result.right.version).toBe("1.0");
    }
  });

  it("allows multiple versions to be saved", async () => {
    const r1 = await savePolicy("1.0", "v1", defaultPolicy.boundary)();
    const r2 = await savePolicy("2.0", "v2", defaultPolicy.boundary)();

    expect(E.isRight(r1)).toBe(true);
    expect(E.isRight(r2)).toBe(true);
    if (E.isRight(r1) && E.isRight(r2)) {
      expect(r1.right.id).not.toBe(r2.right.id);
      expect(r1.right.version).toBe("1.0");
      expect(r2.right.version).toBe("2.0");
    }
  });
});

describe("loadLatestPolicy", () => {
  it("returns undefined when no policy exists", async () => {
    const result = await loadLatestPolicy()();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it("returns latest policy when multiple exist", async () => {
    // 最初のポリシー保存
    await savePolicy("1.0", "old", defaultPolicy.boundary)();
    // 少し待ってから2番目を保存（タイムスタンプを異ならせる）
    await new Promise((resolve) => setTimeout(resolve, 10));
    await savePolicy("2.0", "new", defaultPolicy.boundary)();

    const result = await loadLatestPolicy()();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result) && result.right) {
      expect(result.right.version).toBe("2.0");
      expect(result.right.yaml_content).toBe("new");
    }
  });

  it("correctly deserializes config_json", async () => {
    await savePolicy("1.0", "test", defaultPolicy.boundary)();

    const result = await loadLatestPolicy()();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result) && result.right) {
      expect(result.right.config_json.version).toBe(defaultPolicy.boundary.version);
      expect(result.right.config_json.scopes).toBeDefined();
      expect(result.right.config_json.boundary_classes).toBeDefined();
    }
  });
});

describe("loadPolicyByVersion", () => {
  it("returns undefined when version not found", async () => {
    const result = await loadPolicyByVersion("nonexistent")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBeUndefined();
    }
  });

  it("returns matching policy by version", async () => {
    await savePolicy("1.0", "first", defaultPolicy.boundary)();
    await savePolicy("2.0", "second", defaultPolicy.boundary)();

    const result = await loadPolicyByVersion("1.0")();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result) && result.right) {
      expect(result.right.version).toBe("1.0");
      expect(result.right.yaml_content).toBe("first");
    }
  });
});

describe("hasStoredPolicy", () => {
  it("returns false when no policy exists", async () => {
    const result = await hasStoredPolicy()();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe(false);
    }
  });

  it("returns true when policy exists", async () => {
    await savePolicy("1.0", "test", defaultPolicy.boundary)();

    const result = await hasStoredPolicy()();

    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result)) {
      expect(result.right).toBe(true);
    }
  });
});

describe("Policy persistence integration", () => {
  it("policy survives simulated restart (save → load)", async () => {
    // カスタムポリシーを作成
    const customPolicy = {
      ...defaultPolicy.boundary,
      version: "custom-1.0",
    };

    // 保存
    const saveResult = await savePolicy("custom-1.0", "version: custom-1.0", customPolicy)();
    expect(E.isRight(saveResult)).toBe(true);

    // シミュレートされた再起動後にロード
    const loadResult = await loadLatestPolicy()();
    expect(E.isRight(loadResult)).toBe(true);
    if (E.isRight(loadResult) && loadResult.right) {
      expect(loadResult.right.version).toBe("custom-1.0");
      expect(loadResult.right.config_json.version).toBe("custom-1.0");
    }
  });

  it("latest policy wins after multiple saves", async () => {
    // 複数バージョンを順番に保存
    await savePolicy("1.0", "first", defaultPolicy.boundary)();
    await new Promise((r) => setTimeout(r, 10));
    await savePolicy("2.0", "second", defaultPolicy.boundary)();
    await new Promise((r) => setTimeout(r, 10));
    await savePolicy("3.0", "third", defaultPolicy.boundary)();

    // 最新をロード
    const result = await loadLatestPolicy()();
    expect(E.isRight(result)).toBe(true);
    if (E.isRight(result) && result.right) {
      expect(result.right.version).toBe("3.0");
    }
  });
});

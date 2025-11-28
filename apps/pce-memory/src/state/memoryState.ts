/**
 * PCE Memory モジュールレベル状態管理
 * StateManagerを廃止し、PCEMemoryを直接使用するための状態保持モジュール
 *
 * 設計方針:
 * - モジュールスコープのシングルトン状態
 * - TaskEither操作の直列化キュー
 * - DB永続化との統合
 */
import * as TE from "fp-ts/TaskEither";
import * as E from "fp-ts/Either";
import type { BoundaryPolicy } from "@pce/policy-schemas";
import { defaultPolicy } from "@pce/policy-schemas";
import { PCEMemory, canUpsert, canActivate, canFeedback } from "../domain/stateMachine.js";
import type { PCEState, RuntimeState, RuntimeStateType } from "../domain/stateMachine.js";
import type { DomainError } from "../domain/errors.js";
import { domainError } from "../domain/errors.js";
import { savePolicy, loadLatestPolicy } from "../store/policy.js";
import { countClaims } from "../store/claims.js";

// ========== モジュールスコープ状態 ==========

/** 現在のポリシー */
let currentPolicy: BoundaryPolicy = defaultPolicy.boundary;

/** 現在の状態機械インスタンス */
let currentMachine: PCEMemory<PCEState> = PCEMemory.create();

/** 操作直列化キュー */
let operationQueue: Promise<void> = Promise.resolve();

// ========== 状態アクセサ（読み取り専用）==========

/** 現在のポリシーを取得 */
export function getPolicy(): BoundaryPolicy {
  return currentPolicy;
}

/** 現在のポリシーバージョンを取得 */
export function getPolicyVersion(): string {
  return currentMachine.getPolicyVersion();
}

/** 現在の状態タイプを取得 */
export function getStateType(): RuntimeStateType {
  return currentMachine.getStateType();
}

/** 現在のランタイム状態を取得 */
export function getRuntimeState(): RuntimeState {
  return currentMachine.runtimeState;
}

/** upsert可能かチェック */
export function canDoUpsert(): boolean {
  return canUpsert(currentMachine.runtimeState);
}

/** activate可能かチェック（Ready状態からも可） */
export function canDoActivate(): boolean {
  return canActivate(currentMachine.runtimeState) || currentMachine.runtimeState.type === "Ready";
}

/** feedback可能かチェック */
export function canDoFeedback(): boolean {
  return canFeedback(currentMachine.runtimeState);
}

/**
 * 読み取り操作可能かチェック
 * Query操作はPolicyApplied以降で実行可能（upsertと同じ条件）
 * セマンティックな明確さのため別名として提供
 */
export function canDoQuery(): boolean {
  return canUpsert(currentMachine.runtimeState);
}

/** claim数を取得 */
export function getClaimCount(): number {
  return currentMachine.getClaimCount();
}

/** アクティブコンテキストIDを取得 */
export function getActiveContextId(): string | undefined {
  return currentMachine.getActiveContextId();
}

// ========== 状態遷移操作（TaskEither）==========

/**
 * 操作を直列化キューに追加して実行
 * 並行リクエストによる競合を防止
 */
function enqueue<A>(op: () => Promise<A>): Promise<A> {
  const result = operationQueue.then(op);
  // エラーが発生しても次の操作は実行可能にする
  operationQueue = result.then(() => {}, () => {});
  return result;
}

/**
 * 初期化: DBから状態とポリシーを復元
 * サーバー起動時に1回だけ呼び出す
 */
export function initMemoryState(): TE.TaskEither<DomainError, { state: RuntimeStateType; policyVersion: string }> {
  return () => enqueue(async () => {
    // DBからポリシーをロード
    const policyResult = await loadLatestPolicy()();
    if (E.isLeft(policyResult)) {
      return policyResult;
    }

    const policyRecord = policyResult.right;
    const version = policyRecord?.version ?? defaultPolicy.version ?? "0.1";
    const policy = policyRecord?.config_json ?? defaultPolicy.boundary;

    // DBからclaim数を取得
    const claimCount = await countClaims();

    // 状態を復元
    if (claimCount > 0) {
      currentMachine = PCEMemory.restore({
        type: "HasClaims",
        policyVersion: version,
        claimCount,
      });
    } else if (policyRecord) {
      // ポリシーが保存済みならPolicyApplied状態
      currentMachine = PCEMemory.restore({
        type: "PolicyApplied",
        policyVersion: version,
      });
    } else {
      // 初回起動: Uninitialized状態のまま
      currentMachine = PCEMemory.create();
    }

    currentPolicy = policy;

    return E.right({
      state: currentMachine.getStateType(),
      policyVersion: version,
    });
  });
}

/**
 * ポリシー適用: Uninitialized → PolicyApplied
 * DB永続化を含む
 */
export function applyPolicyOp(yaml?: string): TE.TaskEither<DomainError, { policy_version: string; state: RuntimeStateType }> {
  return () => enqueue(async () => {
    // 状態検証
    if (currentMachine.runtimeState.type !== "Uninitialized") {
      return E.left(domainError(
        "STATE_ERROR",
        `Invalid state: expected Uninitialized, got ${currentMachine.runtimeState.type}`
      ));
    }

    // ポリシーパース
    const { parsePolicy } = await import("@pce/policy-schemas");
    const doc = yaml ? parsePolicy(yaml) : { ok: true, value: defaultPolicy };
    if (!doc.ok || !doc.value) {
      return E.left(domainError("POLICY_INVALID", doc.errors?.join(",") ?? "policy parse failed"));
    }

    const parsedPolicy = doc.value;
    const yamlContent = yaml ?? "";

    // DBに保存
    const saveResult = await savePolicy(parsedPolicy.version, yamlContent, parsedPolicy.boundary)();
    if (E.isLeft(saveResult)) {
      return saveResult;
    }

    // 状態更新
    currentPolicy = parsedPolicy.boundary;
    currentMachine = PCEMemory.restore({
      type: "PolicyApplied",
      policyVersion: parsedPolicy.version,
    });

    return E.right({
      policy_version: parsedPolicy.version,
      state: currentMachine.getStateType(),
    });
  });
}

/**
 * 状態遷移: PolicyApplied | HasClaims → HasClaims
 * upsert成功後に呼び出し
 */
export function transitionToHasClaims(isNew: boolean): void {
  const currentCount = currentMachine.getClaimCount();
  const newClaimCount = isNew ? currentCount + 1 : Math.max(currentCount, 1);
  currentMachine = PCEMemory.restore({
    type: "HasClaims",
    policyVersion: currentMachine.getPolicyVersion(),
    claimCount: newClaimCount,
  });
}

/**
 * 状態遷移: HasClaims | Ready → Ready
 * activate成功後に呼び出し
 */
export function transitionToReady(activeContextId: string): void {
  currentMachine = PCEMemory.restore({
    type: "Ready",
    policyVersion: currentMachine.getPolicyVersion(),
    activeContextId,
  });
}

/**
 * 状態サマリを取得（デバッグ用）
 */
export function getStateSummary(includeDetails: boolean = false): {
  state: RuntimeStateType;
  policy_version: string;
  runtime_state?: RuntimeState;
} {
  if (includeDetails) {
    return {
      state: currentMachine.getStateType(),
      policy_version: currentMachine.getPolicyVersion(),
      runtime_state: currentMachine.runtimeState,
    };
  }
  return {
    state: currentMachine.getStateType(),
    policy_version: currentMachine.getPolicyVersion(),
  };
}

// ========== テスト用リセット ==========

/**
 * 状態をリセット（テスト用）
 */
export function resetMemoryState(): void {
  currentPolicy = defaultPolicy.boundary;
  currentMachine = PCEMemory.create();
  operationQueue = Promise.resolve();
}

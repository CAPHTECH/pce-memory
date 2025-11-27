/**
 * PCE Memory 状態機械API
 * ADR-0002に基づく実装: Phantom Typeで状態遷移を型レベルで強制
 *
 * 状態遷移図:
 * Uninitialized → PolicyApplied → HasClaims → Ready
 *                                    ↑   ↓
 *                                    └───┘ (追加upsert)
 */
import * as TE from "fp-ts/TaskEither";
import * as E from "fp-ts/Either";
import { pipe } from "fp-ts/function";
import type { DomainError } from "./errors.js";
import { domainError } from "./errors.js";

// ========== Phantom Types（コンパイル時の状態表現）==========

/** 初期状態: ポリシー未適用 */
export type Uninitialized = { readonly _tag: "Uninitialized" };

/** ポリシー適用済み: upsert可能 */
export type PolicyApplied = { readonly _tag: "PolicyApplied" };

/** Claims登録済み: activate可能 */
export type HasClaims = { readonly _tag: "HasClaims" };

/** アクティブコンテキスト作成済み: feedback可能 */
export type Ready = { readonly _tag: "Ready" };

/** 全状態の型 */
export type PCEState = Uninitialized | PolicyApplied | HasClaims | Ready;

// 状態遷移の制約型（Phantom Typeパターンでメソッドの`this`型制約に使用）
// Ready状態からもupsert可能（Ready → HasClaims）: 追加claim登録をサポート
type CanUpsert = PolicyApplied | HasClaims | Ready;

// ========== Runtime State（実行時の状態データ）==========

/** 実行時状態の判別型 */
export type RuntimeStateType = "Uninitialized" | "PolicyApplied" | "HasClaims" | "Ready";

/** 実行時状態データ（永続化対象） */
export type RuntimeState =
  | { readonly type: "Uninitialized" }
  | { readonly type: "PolicyApplied"; readonly policyVersion: string }
  | { readonly type: "HasClaims"; readonly policyVersion: string; readonly claimCount: number }
  | { readonly type: "Ready"; readonly policyVersion: string; readonly activeContextId: string };

// ========== 入出力型 ==========

export interface PolicyApplyInput {
  yaml?: string;
}

export interface PolicyApplyResult {
  policyVersion: string;
}

export interface ClaimInput {
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
}

export interface ClaimResult {
  id: string;
  isNew: boolean;
  policyVersion: string;
}

export interface ActivateInput {
  scope: string[];
  allow: string[];
  top_k?: number;
  q?: string;
}

export interface ActivateResult {
  activeContextId: string;
  claims: unknown[];
  policyVersion: string;
}

export interface FeedbackInput {
  claim_id: string;
  signal: "helpful" | "harmful" | "outdated" | "duplicate";
  score?: number;
}

export interface FeedbackResult {
  id: string;
  policyVersion: string;
}

// ========== 状態機械クラス ==========

/**
 * PCEMemory状態機械
 * Phantom Type Sで現在の状態を型レベルで追跡
 *
 * 実装ノート:
 * - `declare protected readonly _phantom: S` はTypeScriptの型システムにのみ存在
 * - JavaScriptコンパイル時に削除され、実行時メモリを消費しない
 * - これにより PCEMemory<StateA> と PCEMemory<StateB> が構造的に区別される
 */
export class PCEMemory<S extends PCEState> {
  // Phantom Type: 型レベルでのみ存在し、実行時にはメモリを消費しない
  declare protected readonly _phantom: S;

  private constructor(
    public readonly runtimeState: RuntimeState
  ) {}

  // ========== ファクトリ ==========

  /** 初期状態を作成 */
  static create(): PCEMemory<Uninitialized> {
    return new PCEMemory({ type: "Uninitialized" });
  }

  /** 実行時状態から復元（外部呼び出し用） */
  static restore(state: RuntimeState): PCEMemory<PCEState> {
    return new PCEMemory(state);
  }

  // ========== 状態遷移メソッド ==========

  /**
   * ポリシー適用: Uninitialized → PolicyApplied
   * @param this Uninitialized状態でのみ呼び出し可能
   */
  applyPolicy(
    this: PCEMemory<Uninitialized>,
    input: PolicyApplyInput,
    applyFn: (yaml?: string) => E.Either<DomainError, string>
  ): TE.TaskEither<DomainError, { machine: PCEMemory<PolicyApplied>; result: PolicyApplyResult }> {
    return pipe(
      TE.fromEither(applyFn(input.yaml)),
      TE.map((version) => ({
        machine: new PCEMemory<PolicyApplied>({
          type: "PolicyApplied",
          policyVersion: version,
        }),
        result: { policyVersion: version },
      }))
    );
  }

  /**
   * Claim登録: PolicyApplied | HasClaims → HasClaims
   * @param this PolicyAppliedまたはHasClaims状態でのみ呼び出し可能
   *
   * 実装ノート: isNewフラグで重複検知
   * - isNew=true: 新規登録 → claimCount+1
   * - isNew=false: 既存レコード → claimCount維持（最低でも1に補正）
   */
  upsert(
    this: PCEMemory<CanUpsert>,
    input: ClaimInput,
    upsertFn: (c: ClaimInput) => TE.TaskEither<DomainError, { id: string; isNew: boolean }>
  ): TE.TaskEither<DomainError, { machine: PCEMemory<HasClaims>; result: ClaimResult }> {
    const policyVersion = this.getPolicyVersion();
    const currentCount = this.getClaimCount();

    return pipe(
      upsertFn(input),
      TE.map(({ id, isNew }) => {
        // isNew=trueの場合のみカウントを増加
        // PolicyApplied(count=0)からの最初のupsertは最低1を保証
        const nextCount = isNew ? currentCount + 1 : Math.max(currentCount, 1);
        return {
          machine: new PCEMemory<HasClaims>({
            type: "HasClaims",
            policyVersion,
            claimCount: nextCount,
          }),
          result: { id, isNew, policyVersion },
        };
      })
    );
  }

  /**
   * アクティブコンテキスト作成: HasClaims → Ready
   * @param this HasClaims状態でのみ呼び出し可能
   */
  activate(
    this: PCEMemory<HasClaims>,
    input: ActivateInput,
    activateFn: (input: ActivateInput) => TE.TaskEither<DomainError, { id: string; claims: unknown[] }>
  ): TE.TaskEither<DomainError, { machine: PCEMemory<Ready>; result: ActivateResult }> {
    const policyVersion = this.getPolicyVersion();

    return pipe(
      activateFn(input),
      TE.map((ac) => ({
        machine: new PCEMemory<Ready>({
          type: "Ready",
          policyVersion,
          activeContextId: ac.id,
        }),
        result: { activeContextId: ac.id, claims: ac.claims, policyVersion },
      }))
    );
  }

  /**
   * フィードバック: Ready → Ready
   * @param this Ready状態でのみ呼び出し可能
   */
  feedback(
    this: PCEMemory<Ready>,
    input: FeedbackInput,
    feedbackFn: (input: FeedbackInput) => TE.TaskEither<DomainError, { id: string }>
  ): TE.TaskEither<DomainError, { machine: PCEMemory<Ready>; result: FeedbackResult }> {
    const policyVersion = this.getPolicyVersion();

    return pipe(
      feedbackFn(input),
      TE.map((fb) => ({
        machine: new PCEMemory<Ready>({
          ...this.runtimeState as { type: "Ready"; policyVersion: string; activeContextId: string },
        }),
        result: { id: fb.id, policyVersion },
      }))
    );
  }

  // ========== ヘルパーメソッド ==========

  /** 現在の状態タイプを取得 */
  getStateType(): RuntimeStateType {
    return this.runtimeState.type;
  }

  /** ポリシーバージョンを取得 */
  getPolicyVersion(): string {
    if (this.runtimeState.type === "Uninitialized") {
      return "0.0";
    }
    return this.runtimeState.policyVersion;
  }

  /** Claim数を取得 */
  getClaimCount(): number {
    if (this.runtimeState.type === "HasClaims") {
      return this.runtimeState.claimCount;
    }
    return 0;
  }

  /** アクティブコンテキストIDを取得 */
  getActiveContextId(): string | undefined {
    if (this.runtimeState.type === "Ready") {
      return this.runtimeState.activeContextId;
    }
    return undefined;
  }
}

// ========== 状態検証ユーティリティ ==========

/** 状態がUninitializedかチェック */
export const isUninitialized = (state: RuntimeState): state is { type: "Uninitialized" } =>
  state.type === "Uninitialized";

/** 状態がPolicyAppliedかチェック */
export const isPolicyApplied = (state: RuntimeState): state is { type: "PolicyApplied"; policyVersion: string } =>
  state.type === "PolicyApplied";

/** 状態がHasClaimsかチェック */
export const isHasClaims = (state: RuntimeState): state is { type: "HasClaims"; policyVersion: string; claimCount: number } =>
  state.type === "HasClaims";

/** 状態がReadyかチェック */
export const isReady = (state: RuntimeState): state is { type: "Ready"; policyVersion: string; activeContextId: string } =>
  state.type === "Ready";

/** upsert可能な状態かチェック（Ready状態からも追加upsert可能） */
export const canUpsert = (state: RuntimeState): boolean =>
  state.type === "PolicyApplied" || state.type === "HasClaims" || state.type === "Ready";

/** activate可能な状態かチェック */
export const canActivate = (state: RuntimeState): boolean =>
  state.type === "HasClaims";

/** feedback可能な状態かチェック */
export const canFeedback = (state: RuntimeState): boolean =>
  state.type === "Ready";

/** 状態エラーを生成 */
export const stateError = (expected: string, actual: RuntimeStateType): DomainError =>
  domainError("VALIDATION_ERROR", `Invalid state: expected ${expected}, got ${actual}`);

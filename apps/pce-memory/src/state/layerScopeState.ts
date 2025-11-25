/**
 * Layer/Scope モジュールレベル状態管理
 * ADR-0001に基づくV2 Effect設計の統合
 *
 * TLA+仕様対応:
 * - layerGraph: Layer依存グラフ（自己依存禁止、循環検出）
 * - activeScopes: アクティブなリソーススコープ
 * - scopeResources: スコープごとのリソース管理
 *
 * 不変条件:
 * - LayerAcyclic: Layer非循環性
 * - ScopedResourceInvariant: スコープ終了時のリソース解放
 * - UniqueOwnership: リソース一意所有権
 */
import * as E from "fp-ts/Either";
import type { DomainError } from "../domain/errors.js";
import {
  type LayerGraph,
  type Capability,
  emptyLayerGraph,
  registerLayer,
  hasCapability,
  dependenciesSatisfied,
} from "../layer/graph.js";
import {
  type ScopeState,
  type ScopeId,
  emptyScopeState,
  enterScope,
  exitScope,
  addResourceToScope,
  isScopeActive,
  getLiveResources,
} from "../layer/scope.js";

// ========== モジュールスコープ状態 ==========

/** 現在のLayer依存グラフ */
let currentLayerGraph: LayerGraph = emptyLayerGraph;

/** 現在のスコープ状態 */
let currentScopeState: ScopeState = emptyScopeState;

// ========== Layer管理（サーバー起動時） ==========

/**
 * システムLayerを登録
 * サーバー起動時にDB、PolicyLoader等をCapabilityとして登録
 *
 * TLA+ RegisterLayerに対応:
 * - 自己依存禁止ガード
 * - 依存関係充足チェック
 * - 循環検出
 */
export function registerSystemLayer(
  name: string,
  provides: ReadonlySet<Capability>,
  requires: ReadonlySet<string>
): E.Either<DomainError, void> {
  const result = registerLayer(currentLayerGraph, name, provides, requires);
  if (E.isRight(result)) {
    currentLayerGraph = result.right;
    return E.right(undefined);
  }
  return E.left(result.left);
}

/**
 * 現在のLayerGraphを取得
 */
export function getLayerGraph(): LayerGraph {
  return currentLayerGraph;
}

/**
 * 特定のCapabilityが利用可能かチェック
 */
export function hasSystemCapability(capability: Capability): boolean {
  return hasCapability(currentLayerGraph, capability);
}

/**
 * 依存関係が満たされているかチェック
 */
export function checkDependencies(requires: ReadonlySet<string>): boolean {
  return dependenciesSatisfied(currentLayerGraph, requires);
}

// ========== Scope管理（リクエストごと） ==========

/**
 * リクエストスコープを開始
 * MCPリクエストの処理開始時に呼び出し
 *
 * TLA+ EnterScopeに対応:
 * - 同一スコープの重複開始を防止
 */
export function enterRequestScope(requestId: string): E.Either<DomainError, ScopeId> {
  const scopeId = `scope_${requestId}`;
  const result = enterScope(currentScopeState, scopeId);
  if (E.isRight(result)) {
    currentScopeState = result.right;
    return E.right(scopeId);
  }
  return E.left(result.left);
}

/**
 * リクエストスコープを終了
 * MCPリクエストの処理完了時に呼び出し
 *
 * TLA+ ExitScopeに対応:
 * - 自動リソース解放
 * - ScopedResourceInvariant保証
 */
export function exitRequestScope(scopeId: ScopeId): E.Either<DomainError, void> {
  const result = exitScope(currentScopeState, scopeId);
  if (E.isRight(result)) {
    currentScopeState = result.right;
    return E.right(undefined);
  }
  return E.left(result.left);
}

/**
 * スコープがアクティブかチェック
 * TLA+の `sid ∈ activeScopes` 制約を実装
 */
export function isInActiveScope(scopeId: ScopeId): boolean {
  return isScopeActive(currentScopeState, scopeId);
}

/**
 * 現在のスコープにリソースを追加
 *
 * TLA+ UniqueOwnershipに対応:
 * - リソースは単一スコープにのみ所属可能
 */
export function addResourceToCurrentScope(
  scopeId: ScopeId,
  resourceId: string
): E.Either<DomainError, void> {
  const result = addResourceToScope(currentScopeState, scopeId, resourceId);
  if (E.isRight(result)) {
    currentScopeState = result.right;
    return E.right(undefined);
  }
  return E.left(result.left);
}

/**
 * 現在のライブリソースを取得
 * アクティブなスコープに属するリソースのみ
 */
export function getCurrentLiveResources(): ReadonlySet<string> {
  return getLiveResources(currentScopeState);
}

// ========== 状態サマリ ==========

/**
 * Layer/Scope状態のサマリを取得
 * デバッグ・モニタリング用
 */
export function getLayerScopeSummary(): {
  layers: string[];
  activeScopes: string[];
  liveResourceCount: number;
} {
  return {
    layers: Array.from(currentLayerGraph.layers.keys()),
    activeScopes: Array.from(currentScopeState.activeScopes),
    liveResourceCount: getLiveResources(currentScopeState).size,
  };
}

/**
 * 現在のスコープ状態を取得（詳細）
 */
export function getScopeState(): ScopeState {
  return currentScopeState;
}

// ========== テスト用リセット ==========

/**
 * Layer/Scope状態をリセット（テスト用）
 */
export function resetLayerScopeState(): void {
  currentLayerGraph = emptyLayerGraph;
  currentScopeState = emptyScopeState;
}

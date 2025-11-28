/**
 * スコープ管理
 * V2 Effect設計: リソースのスコープベース管理
 * TLA+ EnterScope, ExitScope, UniqueOwnershipに対応
 */
import * as E from 'fp-ts/Either';
import type { DomainError } from '../domain/errors.js';
import { scopeNotActiveError, domainError } from '../domain/errors.js';

// ScopeId型
export type ScopeId = string;

// ScopeState（不変データ構造）
export interface ScopeState {
  readonly activeScopes: ReadonlySet<ScopeId>;
  readonly scopeResources: ReadonlyMap<ScopeId, ReadonlySet<string>>; // リソースID
}

// 初期状態
export const emptyScopeState: ScopeState = {
  activeScopes: new Set(),
  scopeResources: new Map(),
};

/**
 * スコープ開始（TLA+ EnterScopeに対応）
 */
export const enterScope = (
  state: ScopeState,
  scopeId: ScopeId
): E.Either<DomainError, ScopeState> => {
  if (state.activeScopes.has(scopeId)) {
    return E.left(domainError('VALIDATION_ERROR', `scope already active: ${scopeId}`));
  }

  const newActiveScopes = new Set(state.activeScopes);
  newActiveScopes.add(scopeId);

  const newScopeResources = new Map(state.scopeResources);
  if (!newScopeResources.has(scopeId)) {
    newScopeResources.set(scopeId, new Set());
  }

  return E.right({
    activeScopes: newActiveScopes,
    scopeResources: newScopeResources,
  });
};

/**
 * スコープ終了（TLA+ ExitScopeに対応）
 * 自動リソース解放
 */
export const exitScope = (
  state: ScopeState,
  scopeId: ScopeId
): E.Either<DomainError, ScopeState> => {
  if (!state.activeScopes.has(scopeId)) {
    return E.left(scopeNotActiveError(scopeId));
  }

  const newActiveScopes = new Set(state.activeScopes);
  newActiveScopes.delete(scopeId);

  // 自動リソース解放（TLA+: scopeResources' = [scopeResources EXCEPT ![sid] = {}]）
  const newScopeResources = new Map(state.scopeResources);
  newScopeResources.set(scopeId, new Set());

  return E.right({
    activeScopes: newActiveScopes,
    scopeResources: newScopeResources,
  });
};

/**
 * リソースをスコープに追加
 * 【修正】一意所有権制約（TLA+ UniqueOwnershipに対応）
 */
export const addResourceToScope = (
  state: ScopeState,
  scopeId: ScopeId,
  resourceId: string
): E.Either<DomainError, ScopeState> => {
  if (!state.activeScopes.has(scopeId)) {
    return E.left(scopeNotActiveError(scopeId));
  }

  // 【修正】一意所有権チェック: リソースが既に他のスコープに属していないか
  for (const [otherScopeId, resources] of state.scopeResources) {
    if (otherScopeId !== scopeId && resources.has(resourceId)) {
      return E.left(
        domainError(
          'VALIDATION_ERROR',
          `resource "${resourceId}" already owned by scope "${otherScopeId}"`
        )
      );
    }
  }

  const currentResources = state.scopeResources.get(scopeId) ?? new Set();
  const newResources = new Set(currentResources);
  newResources.add(resourceId);

  const newScopeResources = new Map(state.scopeResources);
  newScopeResources.set(scopeId, newResources);

  return E.right({
    activeScopes: state.activeScopes,
    scopeResources: newScopeResources,
  });
};

/**
 * スコープがアクティブかチェック
 */
export const isScopeActive = (state: ScopeState, scopeId: ScopeId): boolean => {
  return state.activeScopes.has(scopeId);
};

/**
 * ライブリソース取得（TLA+ LiveResourcesに対応）
 */
export const getLiveResources = (state: ScopeState): ReadonlySet<string> => {
  const liveResources = new Set<string>();
  for (const scopeId of state.activeScopes) {
    const resources = state.scopeResources.get(scopeId);
    if (resources) {
      for (const r of resources) {
        liveResources.add(r);
      }
    }
  }
  return liveResources;
};

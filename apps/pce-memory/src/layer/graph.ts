/**
 * Layer依存グラフ
 * V2 Effect設計（修正済み）: 自己依存禁止 + 循環検出
 * TLA+ RegisterLayerに対応
 */
import * as E from 'fp-ts/Either';
import type { DomainError } from '../domain/errors.js';
import { layerSelfDependencyError, layerCycleError, domainError } from '../domain/errors.js';

// Capability型
export type Capability = 'db_access' | 'schema_validate' | 'policy_check' | 'config_read';

// Layer定義
export interface LayerDef {
  readonly name: string;
  readonly provides: ReadonlySet<Capability>;
  readonly requires: ReadonlySet<string>;
}

// LayerGraph（不変データ構造）
export interface LayerGraph {
  readonly layers: ReadonlyMap<string, LayerDef>;
}

// 空のLayerGraph
export const emptyLayerGraph: LayerGraph = {
  layers: new Map(),
};

/**
 * Layer登録（TLA+ RegisterLayerに対応）
 * 【修正】自己依存禁止ガード追加
 */
export const registerLayer = (
  graph: LayerGraph,
  name: string,
  provides: ReadonlySet<Capability>,
  requires: ReadonlySet<string>
): E.Either<DomainError, LayerGraph> => {
  // 【修正】自己依存チェック（TLA+: name \notin requires）
  if (requires.has(name)) {
    return E.left(layerSelfDependencyError(name));
  }

  // 依存関係充足チェック（TLA+: DependenciesSatisfied）
  for (const dep of requires) {
    if (!graph.layers.has(dep)) {
      return E.left(
        domainError('LAYER_MISSING_DEPENDENCY', `layer "${name}" requires unknown layer "${dep}"`)
      );
    }
  }

  // 循環検出（TLA+: LayerAcyclic）
  // 直接依存のみチェック: l1 ∈ requires(l2) ⇒ l2 ∉ requires(l1)
  for (const dep of requires) {
    const depLayer = graph.layers.get(dep);
    if (depLayer && depLayer.requires.has(name)) {
      return E.left(layerCycleError(name, dep));
    }
  }

  // 新しいLayerGraphを返す（不変）
  const newLayers = new Map(graph.layers);
  newLayers.set(name, { name, provides, requires });

  return E.right({ layers: newLayers });
};

/**
 * 依存関係が満たされているかチェック
 */
export const dependenciesSatisfied = (
  graph: LayerGraph,
  requires: ReadonlySet<string>
): boolean => {
  for (const dep of requires) {
    if (!graph.layers.has(dep)) {
      return false;
    }
  }
  return true;
};

/**
 * Capabilityが利用可能かチェック
 */
export const hasCapability = (graph: LayerGraph, capability: Capability): boolean => {
  for (const layer of graph.layers.values()) {
    if (layer.provides.has(capability)) {
      return true;
    }
  }
  return false;
};

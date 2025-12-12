/**
 * 衝突検出モジュール (Issue #18 Phase 3)
 *
 * G-Set CRDTベースの同期における衝突を検出し、
 * 適切な対応方針を決定する。
 *
 * 衝突種別:
 * - boundary_upgrade: boundary_classの格上げ（自動解決）
 * - entity_content_diff: Entity内容の差分（スキップ）
 * - relation_content_diff: Relation内容の差分（スキップ）
 * - missing_reference: 参照整合性エラー（スキップ）
 */
import { BOUNDARY_STRICTNESS, isBoundaryUpgraded } from './merge.js';
import type {
  BoundaryClass,
  ClaimExport,
  EntityExport,
  RelationExport,
} from './schemas.js';

/**
 * 衝突種別
 */
export type ConflictType =
  | 'boundary_upgrade' // boundary_classの格上げ（自動解決）
  | 'entity_content_diff' // Entity内容の差分（スキップ）
  | 'relation_content_diff' // Relation内容の差分（スキップ）
  | 'missing_reference'; // 参照整合性エラー（スキップ）

/**
 * 解決方法
 */
export type ConflictResolution = 'auto_resolved' | 'skipped';

/**
 * 衝突情報
 */
export interface Conflict {
  type: ConflictType;
  id: string; // 衝突対象のID（content_hash or entity/relation ID）
  localValue?: unknown; // ローカル側の値
  remoteValue?: unknown; // リモート側の値
  resolution: ConflictResolution;
  message: string;
}

/**
 * 衝突検出レポート
 */
export interface ConflictReport {
  conflicts: Conflict[];
  autoResolved: number; // 自動解決された数
  skipped: number; // スキップされた数
}

/**
 * 空の衝突レポートを作成
 */
export function createEmptyConflictReport(): ConflictReport {
  return {
    conflicts: [],
    autoResolved: 0,
    skipped: 0,
  };
}

/**
 * 衝突をレポートに追加
 *
 * @param report 現在のレポート
 * @param conflict 追加する衝突
 * @returns 更新されたレポート（イミュータブル）
 */
export function addConflict(report: ConflictReport, conflict: Conflict): ConflictReport {
  return {
    conflicts: [...report.conflicts, conflict],
    autoResolved:
      conflict.resolution === 'auto_resolved' ? report.autoResolved + 1 : report.autoResolved,
    skipped: conflict.resolution === 'skipped' ? report.skipped + 1 : report.skipped,
  };
}

/**
 * Claimの衝突を検出
 *
 * 同一content_hashで異なるboundary_classの場合:
 * - 格上げ（より厳格になる）の場合: boundary_upgrade として報告、自動解決
 * - 格下げまたは同一の場合: 衝突なし（既存が維持される）
 *
 * @param existing 既存のClaim情報（存在しない場合はundefined）
 * @param incoming インポートされるClaim
 * @returns 衝突情報、または衝突がない場合はnull
 */
export function detectClaimConflict(
  existing: { boundary_class: BoundaryClass } | undefined,
  incoming: ClaimExport
): Conflict | null {
  // 既存がない場合は衝突なし（新規追加）
  if (existing === undefined) {
    return null;
  }

  const existingLevel = BOUNDARY_STRICTNESS[existing.boundary_class];
  const incomingLevel = BOUNDARY_STRICTNESS[incoming.boundary_class];

  // 格上げの場合のみ衝突として報告
  if (isBoundaryUpgraded(existing.boundary_class, incoming.boundary_class)) {
    return {
      type: 'boundary_upgrade',
      id: incoming.content_hash,
      localValue: existing.boundary_class,
      remoteValue: incoming.boundary_class,
      resolution: 'auto_resolved',
      message: `Boundary class upgraded from '${existing.boundary_class}' (level ${existingLevel}) to '${incoming.boundary_class}' (level ${incomingLevel})`,
    };
  }

  // 同一または格下げの場合は衝突なし（既存が維持される）
  return null;
}

/**
 * Entityの衝突を検出
 *
 * 同一IDで異なる内容（name, type, attrs）の場合:
 * - entity_content_diff として報告、スキップ（既存優先）
 *
 * @param existing 既存のEntity（存在しない場合はundefined）
 * @param incoming インポートされるEntity
 * @returns 衝突情報、または衝突がない場合はnull
 */
export function detectEntityConflict(
  existing: EntityExport | undefined,
  incoming: EntityExport
): Conflict | null {
  // 既存がない場合は衝突なし（新規追加）
  if (existing === undefined) {
    return null;
  }

  // 内容が完全に同一かチェック
  const isSame =
    existing.name === incoming.name &&
    existing.type === incoming.type &&
    JSON.stringify(existing.attrs ?? {}) === JSON.stringify(incoming.attrs ?? {}) &&
    existing.canonical_key === incoming.canonical_key;

  if (isSame) {
    return null;
  }

  // 内容が異なる場合は衝突として報告
  return {
    type: 'entity_content_diff',
    id: incoming.id,
    localValue: { name: existing.name, type: existing.type },
    remoteValue: { name: incoming.name, type: incoming.type },
    resolution: 'skipped',
    message: `Entity '${incoming.id}' has different content: local='${existing.name}' (${existing.type}), remote='${incoming.name}' (${incoming.type})`,
  };
}

/**
 * Relationの衝突を検出
 *
 * 同一IDで異なる内容（src_id, dst_id, type, props）の場合:
 * - relation_content_diff として報告、スキップ（既存優先）
 *
 * @param existing 既存のRelation（存在しない場合はundefined）
 * @param incoming インポートされるRelation
 * @returns 衝突情報、または衝突がない場合はnull
 */
export function detectRelationConflict(
  existing: RelationExport | undefined,
  incoming: RelationExport
): Conflict | null {
  // 既存がない場合は衝突なし（新規追加）
  if (existing === undefined) {
    return null;
  }

  // 内容が完全に同一かチェック
  const isSame =
    existing.src_id === incoming.src_id &&
    existing.dst_id === incoming.dst_id &&
    existing.type === incoming.type &&
    JSON.stringify(existing.props ?? {}) === JSON.stringify(incoming.props ?? {}) &&
    existing.evidence_claim_id === incoming.evidence_claim_id;

  if (isSame) {
    return null;
  }

  // 内容が異なる場合は衝突として報告
  return {
    type: 'relation_content_diff',
    id: incoming.id,
    localValue: { src_id: existing.src_id, dst_id: existing.dst_id, type: existing.type },
    remoteValue: { src_id: incoming.src_id, dst_id: incoming.dst_id, type: incoming.type },
    resolution: 'skipped',
    message: `Relation '${incoming.id}' has different content: local=(${existing.src_id}->${existing.dst_id}), remote=(${incoming.src_id}->${incoming.dst_id})`,
  };
}

/**
 * 参照整合性エラーの衝突を作成
 *
 * @param relationId Relation ID
 * @param missingEntityIds 存在しないEntity IDのリスト
 * @returns 衝突情報
 */
export function createMissingReferenceConflict(
  relationId: string,
  missingEntityIds: string[]
): Conflict {
  return {
    type: 'missing_reference',
    id: relationId,
    remoteValue: missingEntityIds,
    resolution: 'skipped',
    message: `Relation '${relationId}' references non-existent entities: ${missingEntityIds.join(', ')}`,
  };
}

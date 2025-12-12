/**
 * マージ戦略実装 (Issue #18)
 *
 * Critical Review指摘事項対応:
 * - boundary_class格下げリスク: 同一content_hashで厳格な方を採用
 * - Entity/RelationのID衝突: ID一致時は既存優先（idempotent）
 */
import type { BoundaryClass } from './schemas.js';

/**
 * 境界クラスの厳格度順序
 * 数値が大きいほど厳格（より機密性が高い）
 */
export const BOUNDARY_STRICTNESS: Record<BoundaryClass, number> = {
  public: 0,
  internal: 1,
  pii: 2,
  secret: 3,
} as const;

/**
 * 2つのboundary_classをマージし、より厳格な方を返す
 *
 * G-Set CRDTの原則に従い、境界クラスは「格上げ」のみ許可し、
 * 「格下げ」は許可しない。これにより、意図しない機密情報の漏洩を防ぐ。
 *
 * @example
 * mergeBoundaryClass('public', 'internal') // => 'internal'
 * mergeBoundaryClass('pii', 'public') // => 'pii'（既存が厳格なので維持）
 *
 * @param existing 既存のboundary_class
 * @param incoming インポートされるboundary_class
 * @returns より厳格なboundary_class
 */
export function mergeBoundaryClass(
  existing: BoundaryClass,
  incoming: BoundaryClass
): BoundaryClass {
  const existingLevel = BOUNDARY_STRICTNESS[existing];
  const incomingLevel = BOUNDARY_STRICTNESS[incoming];

  return incomingLevel > existingLevel ? incoming : existing;
}

/**
 * boundary_classが同期可能かどうかを判定
 *
 * @param boundaryClass 判定対象のboundary_class
 * @param allowedClasses 許可されたboundary_classの配列
 * @returns 同期可能ならtrue
 */
export function isBoundarySyncable(
  boundaryClass: BoundaryClass,
  allowedClasses: BoundaryClass[]
): boolean {
  // secretは常に同期不可
  if (boundaryClass === 'secret') {
    return false;
  }
  return allowedClasses.includes(boundaryClass);
}

/**
 * boundary_classが格上げされたかどうかを判定
 *
 * @param before 変更前のboundary_class
 * @param after 変更後のboundary_class
 * @returns 格上げされた場合はtrue
 */
export function isBoundaryUpgraded(before: BoundaryClass, after: BoundaryClass): boolean {
  return BOUNDARY_STRICTNESS[after] > BOUNDARY_STRICTNESS[before];
}

/**
 * マージ結果の種別
 */
export type MergeAction =
  | 'new' // 新規追加
  | 'skipped_duplicate' // 既存と同一で変更なし
  | 'upgraded_boundary' // boundary_classが格上げされた
  | 'skipped_tombstone'; // tombstoneフラグで除外（Phase 2）

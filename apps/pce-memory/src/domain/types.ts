/**
 * ドメイン型定義
 * 共通の定数と型をエクスポート
 */

/**
 * Entity型の有効な値
 * Graph Memory: Actor, Artifact, Event, Concept
 */
export const ENTITY_TYPES = ["Actor", "Artifact", "Event", "Concept"] as const;

/**
 * Entity型のユニオン型
 */
export type EntityType = (typeof ENTITY_TYPES)[number];

/**
 * Entity型が有効かチェック
 */
export function isValidEntityType(type: unknown): type is EntityType {
  return typeof type === "string" && ENTITY_TYPES.includes(type as EntityType);
}

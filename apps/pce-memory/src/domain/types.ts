/**
 * ドメイン型定義
 * 共通の定数と型をエクスポート
 */

/**
 * Claim kindの有効な値
 */
export const CLAIM_KINDS = ['fact', 'preference', 'task', 'policy_hint'] as const;

/**
 * Claim kindのユニオン型
 */
export type ClaimKind = (typeof CLAIM_KINDS)[number];

/**
 * Memory typeの有効な値
 */
export const MEMORY_TYPES = ['evidence', 'working_state', 'knowledge', 'procedure', 'norm'] as const;

/**
 * Memory typeのユニオン型
 */
export type MemoryType = (typeof MEMORY_TYPES)[number];

/**
 * Activate intentの有効な値
 */
export const ACTIVATE_INTENTS = [
  'resume_task',
  'debug_incident',
  'design_decision',
  'policy_check',
] as const;

/**
 * Activate intentのユニオン型
 */
export type ActivateIntent = (typeof ACTIVATE_INTENTS)[number];

/**
 * Entity型の有効な値
 * Graph Memory: Actor, Artifact, Event, Concept
 */
export const ENTITY_TYPES = ['Actor', 'Artifact', 'Event', 'Concept'] as const;

/**
 * Entity型のユニオン型
 */
export type EntityType = (typeof ENTITY_TYPES)[number];

/**
 * Claim kindが有効かチェック
 */
export function isValidClaimKind(kind: unknown): kind is ClaimKind {
  return typeof kind === 'string' && CLAIM_KINDS.includes(kind as ClaimKind);
}

/**
 * Memory typeが有効かチェック
 */
export function isValidMemoryType(type: unknown): type is MemoryType {
  return typeof type === 'string' && MEMORY_TYPES.includes(type as MemoryType);
}

/**
 * Activate intentが有効かチェック
 */
export function isValidActivateIntent(intent: unknown): intent is ActivateIntent {
  return typeof intent === 'string' && ACTIVATE_INTENTS.includes(intent as ActivateIntent);
}

/**
 * Entity型が有効かチェック
 */
export function isValidEntityType(type: unknown): type is EntityType {
  return typeof type === 'string' && ENTITY_TYPES.includes(type as EntityType);
}

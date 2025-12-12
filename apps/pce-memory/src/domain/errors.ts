/**
 * ドメインエラー型定義
 * V1 Conservative設計: 明示的なエラー型でEither処理を実現
 */

// エラーコード（Tagged Union）
export type ErrorCode =
  | 'POLICY_INVALID'
  | 'UPSERT_FAILED'
  | 'UPSERT_ENTITY_FAILED' // Graph Memory: Entity登録失敗
  | 'UPSERT_RELATION_FAILED' // Graph Memory: Relation登録失敗
  | 'QUERY_ENTITY_FAILED' // Graph Memory: Entity検索失敗
  | 'QUERY_RELATION_FAILED' // Graph Memory: Relation検索失敗
  | 'ACTIVATE_FAILED'
  | 'BOUNDARY_ERROR'
  | 'FEEDBACK_FAILED'
  | 'VALIDATION_ERROR'
  | 'RATE_LIMIT'
  | 'STATE_ERROR' // 状態機械の不正遷移
  | 'LAYER_CYCLE_DETECTED'
  | 'LAYER_SELF_DEPENDENCY'
  | 'LAYER_MISSING_DEPENDENCY'
  | 'SCOPE_NOT_ACTIVE'
  | 'CLAIM_NOT_FOUND'
  | 'DB_ERROR'
  // Sync関連エラー (Issue #18)
  | 'SYNC_PUSH_FAILED' // push実行エラー
  | 'SYNC_PULL_FAILED' // pull実行エラー
  | 'SYNC_VALIDATION_ERROR' // JSONスキーマ/content_hash検証エラー
  | 'SYNC_PATH_ERROR'; // パストラバーサル等のパスエラー

// ドメインエラー型
export interface DomainError {
  readonly _tag: 'DomainError';
  readonly code: ErrorCode;
  readonly message: string;
  readonly cause?: unknown;
}

// エラー生成関数
export const domainError = (code: ErrorCode, message: string, cause?: unknown): DomainError => ({
  _tag: 'DomainError',
  code,
  message,
  cause,
});

// よく使うエラー生成のショートカット
export const validationError = (message: string): DomainError =>
  domainError('VALIDATION_ERROR', message);

export const rateLimitError = (): DomainError => domainError('RATE_LIMIT', 'rate limit exceeded');

export const claimNotFoundError = (id: string): DomainError =>
  domainError('CLAIM_NOT_FOUND', `claim not found: ${id}`);

export const dbError = (cause: unknown): DomainError =>
  domainError('DB_ERROR', 'database operation failed', cause);

export const layerSelfDependencyError = (name: string): DomainError =>
  domainError('LAYER_SELF_DEPENDENCY', `layer "${name}" cannot depend on itself`);

export const layerCycleError = (from: string, to: string): DomainError =>
  domainError('LAYER_CYCLE_DETECTED', `cycle detected: ${from} -> ${to}`);

export const scopeNotActiveError = (scopeId: string): DomainError =>
  domainError('SCOPE_NOT_ACTIVE', `scope not active: ${scopeId}`);

// Sync関連エラー生成関数 (Issue #18)
export const syncPushError = (message: string, cause?: unknown): DomainError =>
  domainError('SYNC_PUSH_FAILED', message, cause);

export const syncPullError = (message: string, cause?: unknown): DomainError =>
  domainError('SYNC_PULL_FAILED', message, cause);

export const syncValidationError = (message: string, cause?: unknown): DomainError =>
  domainError('SYNC_VALIDATION_ERROR', message, cause);

export const syncPathError = (message: string): DomainError =>
  domainError('SYNC_PATH_ERROR', message);

/**
 * Sync機能エクスポート (Issue #18)
 */

// スキーマ
export {
  ScopeSchema,
  BoundaryClassSchema,
  KindSchema,
  EntityTypeSchema,
  ContentHashSchema,
  ProvenanceSchema,
  ClaimExportSchema,
  EntityExportSchema,
  RelationExportSchema,
  ManifestSchema,
  DEFAULT_SCOPE_FILTER,
  DEFAULT_BOUNDARY_FILTER,
  DEFAULT_TARGET_DIR,
  SYNC_BLOCKED_BOUNDARY,
  type Scope,
  type BoundaryClass,
  type Kind,
  type EntityType,
  type Provenance,
  type ClaimExport,
  type EntityExport,
  type RelationExport,
  type Manifest,
} from './schemas.js';

// マージ戦略
export {
  BOUNDARY_STRICTNESS,
  mergeBoundaryClass,
  isBoundarySyncable,
  isBoundaryUpgraded,
  type MergeAction,
} from './merge.js';

// ファイルシステム操作
export {
  validatePath,
  ensureDirectory,
  directoryExists,
  fileExists,
  readJsonFile,
  writeJsonFile,
  listJsonFiles,
  initSyncDirectory,
  contentHashToFileName,
  fileNameToContentHash,
} from './fileSystem.js';

// バリデーション
export {
  validateContentHashMatch,
  validateClaimExport,
  validateEntityExport,
  validateRelationExport,
  validateManifest,
  toDomainError,
  type ValidationResult,
  type ValidationError,
} from './validation.js';

// Push/Pull/Status
export { executePush, type PushOptions, type PushResult } from './push.js';
export { executePull, type PullOptions, type PullResult } from './pull.js';
export { executeStatus, type StatusOptions, type StatusResult } from './status.js';

// 衝突検出 (Phase 3)
export {
  detectClaimConflict,
  detectEntityConflict,
  detectRelationConflict,
  createMissingReferenceConflict,
  createEmptyConflictReport,
  addConflict,
  type ConflictType,
  type ConflictResolution,
  type Conflict,
  type ConflictReport,
} from './conflict.js';

/**
 * 同期機能用zodスキーマ定義 (Issue #18)
 *
 * G-Set CRDTベースの同期のため、インポート時の厳密なバリデーションが重要。
 * content_hashの一致確認、boundary_classの制約等を型レベルで保証する。
 */
import { z } from 'zod';

// スコープ定義
export const ScopeSchema = z.enum(['session', 'project', 'principle']);
export type Scope = z.infer<typeof ScopeSchema>;

// 境界クラス定義
export const BoundaryClassSchema = z.enum(['public', 'internal', 'pii', 'secret']);
export type BoundaryClass = z.infer<typeof BoundaryClassSchema>;

// Kind定義
export const KindSchema = z.enum(['fact', 'preference', 'task', 'policy_hint']);
export type Kind = z.infer<typeof KindSchema>;

// Entity Type定義
export const EntityTypeSchema = z.enum(['Actor', 'Artifact', 'Event', 'Concept']);
export type EntityType = z.infer<typeof EntityTypeSchema>;

// content_hashパターン
export const ContentHashSchema = z.string().regex(/^sha256:[0-9a-f]{64}$/, {
  message: 'content_hash must be in format sha256:<64 hex characters>',
});

// Provenance schema（mcp-tools.md §1.y準拠）
export const ProvenanceSchema = z.object({
  at: z.string(), // ISO8601 datetime (required)
  actor: z.string().optional(),
  git: z
    .object({
      commit: z.string().optional(),
      repo: z.string().optional(),
      url: z.string().optional(),
      files: z.array(z.string()).optional(),
    })
    .optional(),
  url: z.string().optional(),
  note: z.string().optional(),
  signed: z.boolean().optional(),
});
export type Provenance = z.infer<typeof ProvenanceSchema>;

/**
 * Claim Export Schema
 * .pce-shared/claims/<scope>/<content_hash>.json のファイル形式
 */
export const ClaimExportSchema = z.object({
  // 必須フィールド
  text: z.string().min(1).max(10000),
  kind: KindSchema,
  scope: ScopeSchema,
  boundary_class: BoundaryClassSchema,
  content_hash: ContentHashSchema,

  // オプションフィールド
  provenance: ProvenanceSchema.optional(),

  // 将来の拡張（Phase 2: tombstone対応）
  tombstone: z.boolean().optional(),
  tombstone_at: z.string().optional(),
});
export type ClaimExport = z.infer<typeof ClaimExportSchema>;

/**
 * Entity Export Schema
 * .pce-shared/entities/<entity_id>.json のファイル形式
 */
export const EntityExportSchema = z.object({
  id: z.string().min(1).max(256),
  type: EntityTypeSchema,
  name: z.string().min(1).max(1024),
  canonical_key: z.string().optional(),
  attrs: z.record(z.unknown()).optional(),

  // 将来の拡張（Phase 2: tombstone対応）
  tombstone: z.boolean().optional(),
  tombstone_at: z.string().optional(),
});
export type EntityExport = z.infer<typeof EntityExportSchema>;

/**
 * Relation Export Schema
 * .pce-shared/relations/<relation_id>.json のファイル形式
 */
export const RelationExportSchema = z.object({
  id: z.string().min(1).max(256),
  src_id: z.string().min(1).max(256),
  dst_id: z.string().min(1).max(256),
  type: z.string().min(1).max(256),
  props: z.record(z.unknown()).optional(),
  evidence_claim_id: z.string().optional(),

  // 将来の拡張（Phase 2: tombstone対応）
  tombstone: z.boolean().optional(),
  tombstone_at: z.string().optional(),
});
export type RelationExport = z.infer<typeof RelationExportSchema>;

/**
 * Manifest Schema
 * .pce-shared/manifest.json のファイル形式
 *
 * Phase 2拡張: last_pull_at追加（増分同期用）
 */
export const ManifestSchema = z.object({
  version: z.literal('1.0'),
  pce_memory_version: z.string(),
  last_push_at: z.string(),
  last_push_policy_version: z.string().optional(),
  last_pull_at: z.string().optional(), // Phase 2: 増分同期用
});
export type Manifest = z.infer<typeof ManifestSchema>;

// デフォルト値定義
export const DEFAULT_SCOPE_FILTER: Scope[] = ['project', 'principle'];
export const DEFAULT_BOUNDARY_FILTER: BoundaryClass[] = ['public', 'internal'];
export const DEFAULT_TARGET_DIR = '.pce-shared';

// 同期不可の境界クラス（secretは常に除外）
export const SYNC_BLOCKED_BOUNDARY: BoundaryClass[] = ['secret'];

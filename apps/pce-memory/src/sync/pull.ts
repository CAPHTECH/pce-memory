/**
 * Sync Pull実装 (Issue #18)
 *
 * .pce-shared/ディレクトリからローカルDBへインポート
 *
 * Critical Review指摘事項対応:
 * - zodスキーマ検証
 * - content_hash一致検証
 * - boundary_classマージ戦略（格上げのみ許可）
 */
import * as path from 'node:path';
import * as E from 'fp-ts/Either';
import { syncPullError, type DomainError } from '../domain/errors.js';
import {
  upsertClaim,
  findClaimByContentHash,
  updateClaimBoundaryClass,
  type ClaimInput,
} from '../store/claims.js';
import { upsertEntity, findEntityById, type EntityInput } from '../store/entities.js';
import { upsertRelation, findRelationById, type RelationInput } from '../store/relations.js';
import {
  DEFAULT_TARGET_DIR,
  DEFAULT_BOUNDARY_FILTER,
  SYNC_BLOCKED_BOUNDARY,
  type Scope,
  type BoundaryClass,
  type ClaimExport,
  type EntityExport,
  type RelationExport,
} from './schemas.js';
import { directoryExists, readJsonFile, listJsonFiles, validatePath } from './fileSystem.js';
import {
  validateClaimExport,
  validateEntityExport,
  validateRelationExport,
  validateManifest,
  type ValidationError,
} from './validation.js';
import {
  mergeBoundaryClass,
  isBoundarySyncable,
  isBoundaryUpgraded,
  type MergeAction,
} from './merge.js';
import { getPolicyVersion } from '../state/memoryState.js';

/**
 * Pull入力オプション
 */
export interface PullOptions {
  basePath: string; // 基準ディレクトリ（プロジェクトルート）
  sourceDir?: string; // ソースディレクトリ名（デフォルト: .pce-shared）
  scopeFilter?: Scope[]; // スコープフィルター（指定時はそのスコープのみインポート）
  boundaryFilter?: BoundaryClass[]; // 境界クラスフィルター
  dryRun?: boolean; // trueの場合は実際のインポートを行わない
}

/**
 * Pull結果
 */
export interface PullResult {
  imported: {
    claims: {
      new: number;
      skippedDuplicate: number;
      upgradedBoundary: number;
    };
    entities: {
      new: number;
      skippedDuplicate: number;
    };
    relations: {
      new: number;
      skippedDuplicate: number;
    };
  };
  validationErrors: ValidationError[];
  dryRun: boolean;
  policyVersion: string;
}

/**
 * 有効な境界クラスフィルターを計算
 * secretは常に除外
 *
 * デフォルトはpushと同じ値（public, internal）を使用
 * piiはオプトイン（明示的に指定が必要）
 */
function getEffectiveBoundaryFilter(filter?: BoundaryClass[]): BoundaryClass[] {
  const base = filter ?? DEFAULT_BOUNDARY_FILTER;
  return base.filter((bc) => !SYNC_BLOCKED_BOUNDARY.includes(bc));
}

/**
 * ClaimExportをClaimInputに変換
 *
 * exactOptionalPropertyTypes対応:
 * undefinedの値を持つプロパティは設定しない
 */
function toClaimInput(claim: ClaimExport): ClaimInput {
  const input: ClaimInput = {
    text: claim.text,
    kind: claim.kind,
    scope: claim.scope,
    boundary_class: claim.boundary_class,
    content_hash: claim.content_hash,
  };

  // provenanceがある場合のみ設定（undefinedのプロパティは除外）
  if (claim.provenance) {
    const provenance: ClaimInput['provenance'] = {
      at: claim.provenance.at,
    };
    if (claim.provenance.actor !== undefined) {
      provenance.actor = claim.provenance.actor;
    }
    if (claim.provenance.url !== undefined) {
      provenance.url = claim.provenance.url;
    }
    if (claim.provenance.note !== undefined) {
      provenance.note = claim.provenance.note;
    }
    if (claim.provenance.signed !== undefined) {
      provenance.signed = claim.provenance.signed;
    }
    if (claim.provenance.git !== undefined) {
      const git: NonNullable<ClaimInput['provenance']>['git'] = {};
      if (claim.provenance.git.commit !== undefined) {
        git.commit = claim.provenance.git.commit;
      }
      if (claim.provenance.git.repo !== undefined) {
        git.repo = claim.provenance.git.repo;
      }
      if (claim.provenance.git.url !== undefined) {
        git.url = claim.provenance.git.url;
      }
      if (claim.provenance.git.files !== undefined) {
        git.files = claim.provenance.git.files;
      }
      provenance.git = git;
    }
    input.provenance = provenance;
  }

  return input;
}

/**
 * EntityExportをEntityInputに変換
 */
function toEntityInput(entity: EntityExport): EntityInput {
  return {
    id: entity.id,
    type: entity.type,
    name: entity.name,
    ...(entity.canonical_key && { canonical_key: entity.canonical_key }),
    ...(entity.attrs && { attrs: entity.attrs }),
  };
}

/**
 * RelationExportをRelationInputに変換
 */
function toRelationInput(relation: RelationExport): RelationInput {
  return {
    id: relation.id,
    src_id: relation.src_id,
    dst_id: relation.dst_id,
    type: relation.type,
    ...(relation.props && { props: relation.props }),
    ...(relation.evidence_claim_id && { evidence_claim_id: relation.evidence_claim_id }),
  };
}

/**
 * Claimをインポート
 *
 * @returns マージアクションの種別
 */
async function importClaim(
  claim: ClaimExport,
  boundaryFilter: BoundaryClass[],
  dryRun: boolean
): Promise<MergeAction> {
  // 境界クラスフィルターチェック
  if (!isBoundarySyncable(claim.boundary_class, boundaryFilter)) {
    return 'skipped_duplicate';
  }

  // tombstoneチェック（Phase 2対応）
  if (claim.tombstone) {
    return 'skipped_tombstone';
  }

  // 既存Claimを検索
  const existing = await findClaimByContentHash(claim.content_hash);

  if (existing) {
    // 既存がある場合：boundary_classのマージ判定
    const merged = mergeBoundaryClass(
      existing.boundary_class as BoundaryClass,
      claim.boundary_class
    );

    if (isBoundaryUpgraded(existing.boundary_class as BoundaryClass, merged)) {
      // 格上げが必要
      if (!dryRun) {
        await updateClaimBoundaryClass(existing.id, merged);
      }
      return 'upgraded_boundary';
    }

    return 'skipped_duplicate';
  }

  // 新規の場合
  if (!dryRun) {
    await upsertClaim(toClaimInput(claim));
  }
  return 'new';
}

/**
 * Entityをインポート
 *
 * @returns マージアクションの種別
 */
async function importEntity(entity: EntityExport, dryRun: boolean): Promise<MergeAction> {
  // tombstoneチェック（Phase 2対応）
  if (entity.tombstone) {
    return 'skipped_tombstone';
  }

  // 既存Entityを検索
  const existing = await findEntityById(entity.id);

  if (existing) {
    // 既存がある場合はスキップ（ID衝突時は既存優先）
    return 'skipped_duplicate';
  }

  // 新規の場合
  if (!dryRun) {
    await upsertEntity(toEntityInput(entity));
  }
  return 'new';
}

/**
 * Relationをインポート
 *
 * 参照整合性検証:
 * - src_idとdst_idが存在するEntityを参照していることを確認
 * - 参照先が存在しない場合はスキップ（バリデーションエラーとして報告）
 *
 * @returns マージアクションの種別、または参照エラーの場合はValidationError
 */
async function importRelation(
  relation: RelationExport,
  dryRun: boolean
): Promise<MergeAction | { referenceError: string }> {
  // tombstoneチェック（Phase 2対応）
  if (relation.tombstone) {
    return 'skipped_tombstone';
  }

  // 既存Relationを検索
  const existing = await findRelationById(relation.id);

  if (existing) {
    // 既存がある場合はスキップ（ID衝突時は既存優先）
    return 'skipped_duplicate';
  }

  // 参照整合性検証: src_idとdst_idのEntityが存在するか確認
  const srcEntity = await findEntityById(relation.src_id);
  const dstEntity = await findEntityById(relation.dst_id);

  if (!srcEntity && !dstEntity) {
    return {
      referenceError: `Referenced entities not found: src_id=${relation.src_id}, dst_id=${relation.dst_id}`,
    };
  }
  if (!srcEntity) {
    return { referenceError: `Referenced entity not found: src_id=${relation.src_id}` };
  }
  if (!dstEntity) {
    return { referenceError: `Referenced entity not found: dst_id=${relation.dst_id}` };
  }

  // 新規の場合
  if (!dryRun) {
    await upsertRelation(toRelationInput(relation));
  }
  return 'new';
}

/**
 * Sync Pull実行
 *
 * @param options Pull設定
 * @returns 成功時はRight(PullResult)、失敗時はLeft(DomainError)
 */
export async function executePull(
  options: PullOptions
): Promise<E.Either<DomainError, PullResult>> {
  const sourceDir = options.sourceDir ?? DEFAULT_TARGET_DIR;
  const boundaryFilter = getEffectiveBoundaryFilter(options.boundaryFilter);
  const dryRun = options.dryRun ?? false;

  // 1. パス検証
  const validatedPath = validatePath(options.basePath, sourceDir);
  if (E.isLeft(validatedPath)) {
    return validatedPath;
  }
  const syncDir = validatedPath.right;

  // 2. ディレクトリ存在確認
  if (!(await directoryExists(syncDir))) {
    return E.left(syncPullError(`Source directory not found: ${syncDir}`));
  }

  const policyVersion = getPolicyVersion();
  const result: PullResult = {
    imported: {
      claims: { new: 0, skippedDuplicate: 0, upgradedBoundary: 0 },
      entities: { new: 0, skippedDuplicate: 0 },
      relations: { new: 0, skippedDuplicate: 0 },
    },
    validationErrors: [],
    dryRun,
    policyVersion,
  };

  try {
    // 3. manifest.jsonの読み込み（オプション）
    const manifestPath = path.join(syncDir, 'manifest.json');
    const manifestResult = await readJsonFile<unknown>(manifestPath);
    if (E.isRight(manifestResult)) {
      const validationResult = validateManifest(manifestResult.right, manifestPath);
      if (E.isLeft(validationResult)) {
        result.validationErrors.push(validationResult.left);
        // manifest検証エラーは警告として続行
      }
    }

    // 4. Claimsをインポート
    const claimsDir = path.join(syncDir, 'claims');
    if (await directoryExists(claimsDir)) {
      // スコープ別のディレクトリを処理
      const scopes = options.scopeFilter ?? ['project', 'principle'];

      for (const scope of scopes) {
        const scopeDir = path.join(claimsDir, scope);
        if (!(await directoryExists(scopeDir))) {
          continue;
        }

        const claimFiles = await listJsonFiles(scopeDir);

        for (const filePath of claimFiles) {
          // JSONファイルを読み込み
          const fileResult = await readJsonFile<unknown>(filePath);
          if (E.isLeft(fileResult)) {
            result.validationErrors.push({ file: filePath, error: 'Failed to read file' });
            continue;
          }

          // バリデーション
          const validationResult = validateClaimExport(fileResult.right, filePath);
          if (E.isLeft(validationResult)) {
            result.validationErrors.push(validationResult.left);
            continue;
          }

          const claim = validationResult.right;

          // インポート実行
          const action = await importClaim(claim, boundaryFilter, dryRun);

          switch (action) {
            case 'new':
              result.imported.claims.new++;
              break;
            case 'skipped_duplicate':
            case 'skipped_tombstone':
              result.imported.claims.skippedDuplicate++;
              break;
            case 'upgraded_boundary':
              result.imported.claims.upgradedBoundary++;
              break;
          }
        }
      }
    }

    // 5. Entitiesをインポート
    const entitiesDir = path.join(syncDir, 'entities');
    if (await directoryExists(entitiesDir)) {
      const entityFiles = await listJsonFiles(entitiesDir);

      for (const filePath of entityFiles) {
        const fileResult = await readJsonFile<unknown>(filePath);
        if (E.isLeft(fileResult)) {
          result.validationErrors.push({ file: filePath, error: 'Failed to read file' });
          continue;
        }

        const validationResult = validateEntityExport(fileResult.right, filePath);
        if (E.isLeft(validationResult)) {
          result.validationErrors.push(validationResult.left);
          continue;
        }

        const entity = validationResult.right;
        const action = await importEntity(entity, dryRun);

        switch (action) {
          case 'new':
            result.imported.entities.new++;
            break;
          case 'skipped_duplicate':
          case 'skipped_tombstone':
            result.imported.entities.skippedDuplicate++;
            break;
        }
      }
    }

    // 6. Relationsをインポート
    const relationsDir = path.join(syncDir, 'relations');
    if (await directoryExists(relationsDir)) {
      const relationFiles = await listJsonFiles(relationsDir);

      for (const filePath of relationFiles) {
        const fileResult = await readJsonFile<unknown>(filePath);
        if (E.isLeft(fileResult)) {
          result.validationErrors.push({ file: filePath, error: 'Failed to read file' });
          continue;
        }

        const validationResult = validateRelationExport(fileResult.right, filePath);
        if (E.isLeft(validationResult)) {
          result.validationErrors.push(validationResult.left);
          continue;
        }

        const relation = validationResult.right;
        const action = await importRelation(relation, dryRun);

        // 参照エラーの場合はバリデーションエラーとして報告
        if (typeof action === 'object' && 'referenceError' in action) {
          result.validationErrors.push({ file: filePath, error: action.referenceError });
          continue;
        }

        switch (action) {
          case 'new':
            result.imported.relations.new++;
            break;
          case 'skipped_duplicate':
          case 'skipped_tombstone':
            result.imported.relations.skippedDuplicate++;
            break;
        }
      }
    }

    return E.right(result);
  } catch (error) {
    return E.left(syncPullError('Pull execution failed', error));
  }
}

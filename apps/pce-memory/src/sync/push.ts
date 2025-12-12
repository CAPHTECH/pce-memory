/**
 * Sync Push実装 (Issue #18)
 *
 * ローカルDBから.pce-shared/ディレクトリへエクスポート
 */
import * as path from 'node:path';
import * as E from 'fp-ts/Either';
import { syncPushError, type DomainError } from '../domain/errors.js';
import { listClaimsByFilter, type Claim } from '../store/claims.js';
import { listAllEntities, getEntitiesForClaim, type Entity } from '../store/entities.js';
import { listAllRelations, type Relation } from '../store/relations.js';
import {
  DEFAULT_SCOPE_FILTER,
  DEFAULT_BOUNDARY_FILTER,
  DEFAULT_TARGET_DIR,
  SYNC_BLOCKED_BOUNDARY,
  type Scope,
  type BoundaryClass,
  type ClaimExport,
  type EntityExport,
  type RelationExport,
  type Manifest,
} from './schemas.js';
import { initSyncDirectory, writeJsonFile, contentHashToFileName } from './fileSystem.js';
import { isBoundarySyncable } from './merge.js';
import { resolveDefaultTargetDir } from './resolveDefaultTargetDir.js';
import { getPolicyVersion } from '../state/memoryState.js';

// package.jsonからバージョンを取得するためのプレースホルダー
const PCE_MEMORY_VERSION = '0.7.0';

/**
 * Push入力オプション
 */
export interface PushOptions {
  basePath: string; // 基準ディレクトリ（プロジェクトルート）
  targetDir?: string; // 対象ディレクトリ名（デフォルト: .pce-shared）
  scopeFilter?: Scope[]; // スコープフィルター
  boundaryFilter?: BoundaryClass[]; // 境界クラスフィルター
  since?: Date; // 増分エクスポート用の日時
  includeEntities?: boolean; // Entityをエクスポートするか
  includeRelations?: boolean; // Relationをエクスポートするか
}

/**
 * Push結果
 */
export interface PushResult {
  exported: {
    claims: number;
    entities: number;
    relations: number;
  };
  targetDir: string;
  manifestUpdated: boolean;
  policyVersion: string;
}

/**
 * ClaimをClaimExport形式に変換
 */
function toClaimExport(claim: Claim): ClaimExport {
  return {
    text: claim.text,
    kind: claim.kind as ClaimExport['kind'],
    scope: claim.scope as ClaimExport['scope'],
    boundary_class: claim.boundary_class as ClaimExport['boundary_class'],
    content_hash: claim.content_hash,
    ...(claim.provenance && { provenance: claim.provenance }),
  };
}

/**
 * EntityをEntityExport形式に変換
 */
function toEntityExport(entity: Entity): EntityExport {
  return {
    id: entity.id,
    type: entity.type,
    name: entity.name,
    ...(entity.canonical_key && { canonical_key: entity.canonical_key }),
    ...(entity.attrs && { attrs: entity.attrs }),
  };
}

/**
 * RelationをRelationExport形式に変換
 */
function toRelationExport(relation: Relation): RelationExport {
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
 * 有効な境界クラスフィルターを計算
 * secretは常に除外
 */
function getEffectiveBoundaryFilter(filter?: BoundaryClass[]): BoundaryClass[] {
  const base = filter ?? DEFAULT_BOUNDARY_FILTER;
  return base.filter((bc) => !SYNC_BLOCKED_BOUNDARY.includes(bc));
}

/**
 * Sync Push実行
 *
 * @param options Push設定
 * @returns 成功時はRight(PushResult)、失敗時はLeft(DomainError)
 */
export async function executePush(
  options: PushOptions
): Promise<E.Either<DomainError, PushResult>> {
  let basePath = options.basePath;
  let targetDir = options.targetDir ?? DEFAULT_TARGET_DIR;
  if (options.targetDir === undefined) {
    const resolved = await resolveDefaultTargetDir(options.basePath);
    basePath = resolved.basePath;
    targetDir = resolved.targetDir;
  }

  const scopeFilter = options.scopeFilter ?? DEFAULT_SCOPE_FILTER;
  const boundaryFilter = getEffectiveBoundaryFilter(options.boundaryFilter);
  const includeEntities = options.includeEntities ?? true;
  const includeRelations = options.includeRelations ?? true;

  // 1. ディレクトリ初期化
  const initResult = await initSyncDirectory(basePath, targetDir);
  if (E.isLeft(initResult)) {
    return initResult;
  }
  const syncDir = initResult.right;

  try {
    let exportedClaims = 0;
    let exportedEntities = 0;
    let exportedRelations = 0;

    // エクスポート対象のEntityのIDを収集（Claimに関連するもののみ）
    const exportedEntityIds = new Set<string>();

    // 2. Claimをエクスポート
    const claims = await listClaimsByFilter({
      scopes: scopeFilter,
      boundaryClasses: boundaryFilter,
      ...(options.since !== undefined && { since: options.since }),
    });

    for (const claim of claims) {
      // 境界クラスが同期可能か確認
      if (!isBoundarySyncable(claim.boundary_class as BoundaryClass, boundaryFilter)) {
        continue;
      }

      const claimExport = toClaimExport(claim);
      const fileName = contentHashToFileName(claim.content_hash);
      const filePath = path.join(syncDir, 'claims', claim.scope, fileName);

      const writeResult = await writeJsonFile(filePath, claimExport);
      if (E.isLeft(writeResult)) {
        return E.left(syncPushError(`Failed to write claim: ${claim.id}`, writeResult.left));
      }

      exportedClaims++;

      // このClaimに関連するEntityのIDを収集
      if (includeEntities) {
        const entities = await getEntitiesForClaim(claim.id);
        for (const entity of entities) {
          exportedEntityIds.add(entity.id);
        }
      }
    }

    // 3. Entityをエクスポート（Claimに関連するもののみ）
    // Note: sinceはClaimフィルタにのみ使用。参照されるEntity/Relationは常にエクスポート（参照整合性確保）
    if (includeEntities && exportedEntityIds.size > 0) {
      const allEntities = await listAllEntities();
      for (const entity of allEntities) {
        if (!exportedEntityIds.has(entity.id)) {
          continue;
        }

        const entityExport = toEntityExport(entity);
        const filePath = path.join(syncDir, 'entities', `${entity.id}.json`);

        const writeResult = await writeJsonFile(filePath, entityExport);
        if (E.isLeft(writeResult)) {
          return E.left(syncPushError(`Failed to write entity: ${entity.id}`, writeResult.left));
        }

        exportedEntities++;
      }
    }

    // 4. Relationをエクスポート（Entityに関連するもののみ）
    // Note: sinceはClaimフィルタにのみ使用。参照されるEntity/Relationは常にエクスポート（参照整合性確保）
    if (includeRelations && exportedEntityIds.size > 0) {
      const allRelations = await listAllRelations();
      for (const relation of allRelations) {
        // src_idまたはdst_idがエクスポート対象のEntityに含まれる場合のみ
        if (!exportedEntityIds.has(relation.src_id) && !exportedEntityIds.has(relation.dst_id)) {
          continue;
        }

        const relationExport = toRelationExport(relation);
        const filePath = path.join(syncDir, 'relations', `${relation.id}.json`);

        const writeResult = await writeJsonFile(filePath, relationExport);
        if (E.isLeft(writeResult)) {
          return E.left(
            syncPushError(`Failed to write relation: ${relation.id}`, writeResult.left)
          );
        }

        exportedRelations++;
      }
    }

    // 5. manifest.jsonを更新
    const policyVersion = getPolicyVersion();
    const manifest: Manifest = {
      version: '1.0',
      pce_memory_version: PCE_MEMORY_VERSION,
      last_push_at: new Date().toISOString(),
      last_push_policy_version: policyVersion,
    };

    const manifestPath = path.join(syncDir, 'manifest.json');
    const manifestResult = await writeJsonFile(manifestPath, manifest);
    if (E.isLeft(manifestResult)) {
      return E.left(syncPushError('Failed to write manifest.json', manifestResult.left));
    }

    return E.right({
      exported: {
        claims: exportedClaims,
        entities: exportedEntities,
        relations: exportedRelations,
      },
      targetDir: syncDir,
      manifestUpdated: true,
      policyVersion,
    });
  } catch (error) {
    return E.left(syncPushError('Push execution failed', error));
  }
}

/**
 * Sync Status実装 (Issue #18 Phase 2)
 *
 * 同期ディレクトリの状態を確認するツール
 */
import * as path from 'node:path';
import * as E from 'fp-ts/Either';
import { syncStatusError, type DomainError } from '../domain/errors.js';
import { directoryExists, readJsonFile, listJsonFiles, validatePath } from './fileSystem.js';
import { validateManifest } from './validation.js';
import { DEFAULT_TARGET_DIR, type Manifest } from './schemas.js';
import { resolveDefaultTargetDir } from './resolveDefaultTargetDir.js';
import { getPolicyVersion } from '../state/memoryState.js';

/**
 * Status入力オプション
 */
export interface StatusOptions {
  basePath: string; // 基準ディレクトリ（プロジェクトルート）
  targetDir?: string; // 対象ディレクトリ名（デフォルト: .pce-shared）
}

/**
 * Status結果
 */
export interface StatusResult {
  exists: boolean; // 同期ディレクトリが存在するか
  manifest?: Manifest; // manifest.jsonの内容（存在する場合）
  files: {
    claims: number; // Claimファイル数
    entities: number; // Entityファイル数
    relations: number; // Relationファイル数
  };
  validation: {
    isValid: boolean; // バリデーション成功フラグ
    errors: string[]; // バリデーションエラー一覧
  };
  targetDir: string; // 確認したディレクトリパス
  policyVersion: string; // 現在のポリシーバージョン
}

/**
 * Sync Status実行
 *
 * @param options Status設定
 * @returns 成功時はRight(StatusResult)、失敗時はLeft(DomainError)
 */
export async function executeStatus(
  options: StatusOptions
): Promise<E.Either<DomainError, StatusResult>> {
  let basePath = options.basePath;
  let targetDir = options.targetDir ?? DEFAULT_TARGET_DIR;
  if (options.targetDir === undefined) {
    const resolved = await resolveDefaultTargetDir(options.basePath);
    basePath = resolved.basePath;
    targetDir = resolved.targetDir;
  }

  // 1. パス検証
  const validatedPath = validatePath(basePath, targetDir);
  if (E.isLeft(validatedPath)) {
    return validatedPath;
  }
  const syncDir = validatedPath.right;

  const policyVersion = getPolicyVersion();

  // 2. ディレクトリ存在確認
  if (!(await directoryExists(syncDir))) {
    return E.right({
      exists: false,
      files: { claims: 0, entities: 0, relations: 0 },
      validation: { isValid: true, errors: [] },
      targetDir: syncDir,
      policyVersion,
    });
  }

  try {
    const errors: string[] = [];
    let manifestData: Manifest | undefined;

    // 3. manifest.json読み込み
    const manifestPath = path.join(syncDir, 'manifest.json');
    const manifestResult = await readJsonFile<unknown>(manifestPath);
    if (E.isRight(manifestResult)) {
      const validationResult = validateManifest(manifestResult.right, manifestPath);
      if (E.isRight(validationResult)) {
        manifestData = validationResult.right;
      } else {
        errors.push(validationResult.left.error);
      }
    }
    // manifest.jsonが存在しない場合はエラーとしない（空のディレクトリも許容）

    // 4. Claimファイル数カウント
    const claimsDir = path.join(syncDir, 'claims');
    let claimCount = 0;
    if (await directoryExists(claimsDir)) {
      // project, principleの各スコープディレクトリをカウント
      const projectClaims = await listJsonFiles(path.join(claimsDir, 'project'));
      const principleClaims = await listJsonFiles(path.join(claimsDir, 'principle'));
      // sessionスコープも確認（通常は空）
      const sessionClaims = await listJsonFiles(path.join(claimsDir, 'session'));
      claimCount = projectClaims.length + principleClaims.length + sessionClaims.length;
    }

    // 5. Entityファイル数カウント
    const entitiesDir = path.join(syncDir, 'entities');
    const entityCount = (await directoryExists(entitiesDir))
      ? (await listJsonFiles(entitiesDir)).length
      : 0;

    // 6. Relationファイル数カウント
    const relationsDir = path.join(syncDir, 'relations');
    const relationCount = (await directoryExists(relationsDir))
      ? (await listJsonFiles(relationsDir)).length
      : 0;

    // exactOptionalPropertyTypes対応: manifestは存在する場合のみ設定
    return E.right({
      exists: true,
      ...(manifestData && { manifest: manifestData }),
      files: {
        claims: claimCount,
        entities: entityCount,
        relations: relationCount,
      },
      validation: {
        isValid: errors.length === 0,
        errors,
      },
      targetDir: syncDir,
      policyVersion,
    });
  } catch (error) {
    return E.left(syncStatusError('Status check failed', error));
  }
}

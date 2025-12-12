/**
 * ファイルシステム操作 (Issue #18)
 *
 * セキュリティ考慮事項:
 * - パストラバーサル攻撃の防止
 * - 安全なディレクトリ作成
 * - JSONファイルの読み書き
 */
import * as fs from 'node:fs/promises';
import * as path from 'node:path';
import * as E from 'fp-ts/Either';
import { syncPathError, type DomainError } from '../domain/errors.js';

/**
 * パスが安全かどうかを検証（パストラバーサル防止）
 *
 * @param basePath 基準となるディレクトリ
 * @param targetPath 検証対象のパス
 * @returns 安全な場合はRight(正規化されたパス)、危険な場合はLeft(エラー)
 */
export function validatePath(basePath: string, targetPath: string): E.Either<DomainError, string> {
  const resolvedBase = path.resolve(basePath);
  const resolvedTarget = path.resolve(basePath, targetPath);

  // 正規化後のパスが基準ディレクトリ配下にあることを確認
  if (!resolvedTarget.startsWith(resolvedBase + path.sep) && resolvedTarget !== resolvedBase) {
    return E.left(syncPathError(`Path traversal detected: ${targetPath}`));
  }

  return E.right(resolvedTarget);
}

/**
 * ディレクトリが存在することを確認し、なければ作成
 *
 * @param dirPath 作成するディレクトリパス
 * @returns 成功時はRight(void)、失敗時はLeft(エラー)
 */
export async function ensureDirectory(dirPath: string): Promise<E.Either<DomainError, void>> {
  try {
    await fs.mkdir(dirPath, { recursive: true });
    return E.right(undefined);
  } catch (error) {
    return E.left(syncPathError(`Failed to create directory: ${dirPath}`));
  }
}

/**
 * ディレクトリが存在するかどうかを確認
 *
 * @param dirPath 確認するディレクトリパス
 * @returns 存在する場合はtrue
 */
export async function directoryExists(dirPath: string): Promise<boolean> {
  try {
    const stat = await fs.stat(dirPath);
    return stat.isDirectory();
  } catch {
    return false;
  }
}

/**
 * ファイルが存在するかどうかを確認
 *
 * @param filePath 確認するファイルパス
 * @returns 存在する場合はtrue
 */
export async function fileExists(filePath: string): Promise<boolean> {
  try {
    const stat = await fs.stat(filePath);
    return stat.isFile();
  } catch {
    return false;
  }
}

/**
 * JSONファイルを読み込み
 *
 * @param filePath 読み込むファイルパス
 * @returns 成功時はRight(パース済みオブジェクト)、失敗時はLeft(エラー)
 */
export async function readJsonFile<T>(filePath: string): Promise<E.Either<DomainError, T>> {
  try {
    const content = await fs.readFile(filePath, 'utf-8');
    const parsed = JSON.parse(content) as T;
    return E.right(parsed);
  } catch (error) {
    return E.left(syncPathError(`Failed to read JSON file: ${filePath}`));
  }
}

/**
 * JSONファイルを書き込み
 *
 * @param filePath 書き込むファイルパス
 * @param data 書き込むデータ
 * @returns 成功時はRight(void)、失敗時はLeft(エラー)
 */
export async function writeJsonFile<T>(filePath: string, data: T): Promise<E.Either<DomainError, void>> {
  try {
    // ディレクトリが存在することを確認
    const dir = path.dirname(filePath);
    await fs.mkdir(dir, { recursive: true });

    // 整形されたJSONを書き込み（可読性とGit差分のため）
    const content = JSON.stringify(data, null, 2);
    await fs.writeFile(filePath, content, 'utf-8');
    return E.right(undefined);
  } catch (error) {
    return E.left(syncPathError(`Failed to write JSON file: ${filePath}`));
  }
}

/**
 * ディレクトリ内のJSONファイル一覧を取得
 *
 * @param dirPath 検索するディレクトリパス
 * @param recursive サブディレクトリも検索するか
 * @returns JSONファイルパスの配列
 */
export async function listJsonFiles(dirPath: string, recursive: boolean = false): Promise<string[]> {
  const results: string[] = [];

  try {
    const entries = await fs.readdir(dirPath, { withFileTypes: true });

    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);

      if (entry.isDirectory() && recursive) {
        const subFiles = await listJsonFiles(fullPath, recursive);
        results.push(...subFiles);
      } else if (entry.isFile() && entry.name.endsWith('.json')) {
        results.push(fullPath);
      }
    }
  } catch {
    // ディレクトリが存在しない場合は空配列を返す
  }

  return results;
}

/**
 * .pce-shared/ディレクトリの標準構造を作成
 *
 * @param basePath 基準ディレクトリ（通常はプロジェクトルート）
 * @param targetDir 対象ディレクトリ名（デフォルト: .pce-shared）
 * @returns 成功時はRight(作成されたディレクトリパス)、失敗時はLeft(エラー)
 */
export async function initSyncDirectory(
  basePath: string,
  targetDir: string = '.pce-shared'
): Promise<E.Either<DomainError, string>> {
  // パス検証
  const validatedPath = validatePath(basePath, targetDir);
  if (E.isLeft(validatedPath)) {
    return validatedPath;
  }

  const syncDir = validatedPath.right;

  // ディレクトリ構造を作成
  const dirs = [
    syncDir,
    path.join(syncDir, 'claims', 'project'),
    path.join(syncDir, 'claims', 'principle'),
    path.join(syncDir, 'entities'),
    path.join(syncDir, 'relations'),
  ];

  for (const dir of dirs) {
    const result = await ensureDirectory(dir);
    if (E.isLeft(result)) {
      return result;
    }
  }

  return E.right(syncDir);
}

/**
 * content_hashからファイル名を生成
 * sha256:xxxx... → xxxx....json
 *
 * @param contentHash content_hash値
 * @returns ファイル名（.json付き）
 */
export function contentHashToFileName(contentHash: string): string {
  // "sha256:" プレフィックスを除去
  const hash = contentHash.replace(/^sha256:/, '');
  return `${hash}.json`;
}

/**
 * ファイル名からcontent_hashを復元
 * xxxx....json → sha256:xxxx...
 *
 * @param fileName ファイル名
 * @returns content_hash値
 */
export function fileNameToContentHash(fileName: string): string {
  const hash = fileName.replace(/\.json$/, '');
  return `sha256:${hash}`;
}

/**
 * 同期データ検証 (Issue #18)
 *
 * Critical Review指摘事項対応:
 * - pull時のJSON検証不足: zodスキーマ + content_hash一致検証
 * - content_hashの改竄検知
 */
import * as E from 'fp-ts/Either';
import type { z } from 'zod';
import { computeContentHash } from '@pce/embeddings';
import { syncValidationError, type DomainError } from '../domain/errors.js';
import {
  ClaimExportSchema,
  EntityExportSchema,
  RelationExportSchema,
  ManifestSchema,
  type ClaimExport,
  type EntityExport,
  type RelationExport,
  type Manifest,
} from './schemas.js';

/**
 * 検証結果の型
 */
export interface ValidationResult<T> {
  data: T;
  file: string;
}

/**
 * 検証エラーの型
 */
export interface ValidationError {
  file: string;
  error: string;
}

/**
 * zodスキーマでデータを検証
 *
 * @param schema zodスキーマ
 * @param data 検証対象データ
 * @param file ファイルパス（エラーメッセージ用）
 * @returns 成功時はRight(検証済みデータ)、失敗時はLeft(エラー)
 */
function validateWithSchema<T>(
  schema: z.ZodSchema<T>,
  data: unknown,
  file: string
): E.Either<ValidationError, T> {
  const result = schema.safeParse(data);

  if (!result.success) {
    const errorMessages = result.error.errors.map((e) => `${e.path.join('.')}: ${e.message}`).join('; ');
    return E.left({ file, error: `Schema validation failed: ${errorMessages}` });
  }

  return E.right(result.data);
}

/**
 * content_hashとテキストの一致を検証
 *
 * 改竄検知のため、保存されているcontent_hashと
 * 実際のテキストから計算したハッシュが一致するか確認する。
 *
 * @param text テキスト
 * @param expectedHash 期待されるcontent_hash
 * @param file ファイルパス（エラーメッセージ用）
 * @returns 成功時はRight(void)、失敗時はLeft(エラー)
 */
export function validateContentHashMatch(
  text: string,
  expectedHash: string,
  file: string
): E.Either<ValidationError, void> {
  const computedHash = `sha256:${computeContentHash(text)}`;

  if (computedHash !== expectedHash) {
    return E.left({
      file,
      error: `Content hash mismatch: expected ${expectedHash}, computed ${computedHash}`,
    });
  }

  return E.right(undefined);
}

/**
 * Claimデータを検証
 *
 * 1. zodスキーマ検証
 * 2. content_hash一致検証
 *
 * @param data 検証対象データ
 * @param file ファイルパス
 * @returns 成功時はRight(検証済みClaim)、失敗時はLeft(エラー)
 */
export function validateClaimExport(
  data: unknown,
  file: string
): E.Either<ValidationError, ClaimExport> {
  // 1. zodスキーマ検証
  const schemaResult = validateWithSchema(ClaimExportSchema, data, file);
  if (E.isLeft(schemaResult)) {
    return schemaResult;
  }

  const claim = schemaResult.right;

  // 2. content_hash一致検証
  const hashResult = validateContentHashMatch(claim.text, claim.content_hash, file);
  if (E.isLeft(hashResult)) {
    return hashResult;
  }

  return E.right(claim);
}

/**
 * Entityデータを検証
 *
 * @param data 検証対象データ
 * @param file ファイルパス
 * @returns 成功時はRight(検証済みEntity)、失敗時はLeft(エラー)
 */
export function validateEntityExport(
  data: unknown,
  file: string
): E.Either<ValidationError, EntityExport> {
  return validateWithSchema(EntityExportSchema, data, file);
}

/**
 * Relationデータを検証
 *
 * @param data 検証対象データ
 * @param file ファイルパス
 * @returns 成功時はRight(検証済みRelation)、失敗時はLeft(エラー)
 */
export function validateRelationExport(
  data: unknown,
  file: string
): E.Either<ValidationError, RelationExport> {
  return validateWithSchema(RelationExportSchema, data, file);
}

/**
 * Manifestデータを検証
 *
 * @param data 検証対象データ
 * @param file ファイルパス
 * @returns 成功時はRight(検証済みManifest)、失敗時はLeft(エラー)
 */
export function validateManifest(
  data: unknown,
  file: string
): E.Either<ValidationError, Manifest> {
  return validateWithSchema(ManifestSchema, data, file);
}

/**
 * ValidationErrorをDomainErrorに変換
 */
export function toDomainError(error: ValidationError): DomainError {
  return syncValidationError(`${error.file}: ${error.error}`);
}

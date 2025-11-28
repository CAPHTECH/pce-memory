/**
 * @pce/embeddings Redact処理
 * Alloy RedactBeforeEmbed: Confidentialデータは埋め込み前にredact必須
 */

import * as E from 'fp-ts/Either';
import { boundaryValidate } from '@pce/boundary';
import type { BoundaryPolicy } from '@pce/policy-schemas';
import { defaultPolicy } from '@pce/policy-schemas';
import type { SensitivityLevel } from './types.js';
import { computeContentHash } from './hash.js';

/**
 * 埋め込み用に準備されたテキスト
 */
export interface PreparedText {
  /** 処理済みテキスト（redact済みの場合あり） */
  readonly text: string;
  /** 元テキスト */
  readonly originalText: string;
  /** コンテンツハッシュ（処理済みテキストのハッシュ） */
  readonly hash: string;
  /** redact処理が適用されたか */
  readonly wasRedacted: boolean;
}

/**
 * Redactエラー
 */
export interface RedactError {
  readonly _tag: 'RedactError';
  readonly message: string;
  readonly cause?: unknown;
}

export const redactError = (message: string, cause?: unknown): RedactError => ({
  _tag: 'RedactError',
  message,
  cause,
});

/**
 * Alloy RedactBeforeEmbed: Confidentialデータは埋め込み前にredact
 *
 * 機密レベルに応じた処理:
 * - public/internal: そのまま使用
 * - confidential: BoundaryPolicy.redactパターンでredact
 *
 * @param text 元テキスト
 * @param sensitivity 機密レベル
 * @param policy Boundaryポリシー（デフォルト使用可）
 * @returns 処理済みテキストとハッシュ
 */
export const prepareForEmbedding = (
  text: string,
  sensitivity: SensitivityLevel,
  policy: BoundaryPolicy = defaultPolicy.boundary
): E.Either<RedactError, PreparedText> => {
  // Alloy fact: Confidential -> MUST redact
  if (sensitivity === 'confidential') {
    return applyRedact(text, policy);
  }

  // public/internal: そのまま使用
  const hash = computeContentHash(text);
  return E.right({
    text,
    originalText: text,
    hash,
    wasRedacted: false,
  });
};

/**
 * Redact処理を適用
 */
const applyRedact = (text: string, policy: BoundaryPolicy): E.Either<RedactError, PreparedText> => {
  try {
    // BoundaryValidateを使用してredact
    // confidentialデータは全てredact対象
    const result = boundaryValidate(
      {
        payload: text,
        allow: ['*'], // 全アクションを許可（redact処理のみが目的）
        scope: 'session',
      },
      policy
    );

    // redactが適用されなかった場合でも、最低限のパターンでredact
    const redactedText = result.redacted ?? applyDefaultRedactPatterns(text);
    const hash = computeContentHash(redactedText);

    return E.right({
      text: redactedText,
      originalText: text,
      hash,
      wasRedacted: redactedText !== text,
    });
  } catch (e) {
    return E.left(redactError('Redact processing failed', e));
  }
};

/**
 * デフォルトのredactパターンを適用
 * メールアドレス、電話番号などの一般的なPII
 */
const applyDefaultRedactPatterns = (text: string): string => {
  const patterns: RegExp[] = [
    // メールアドレス
    /\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b/gi,
    // 電話番号（日本形式）
    /\b\d{2,4}[- ]?\d{2,4}[- ]?\d{3,4}\b/g,
    // クレジットカード番号（16桁）
    /\b\d{4}[- ]?\d{4}[- ]?\d{4}[- ]?\d{4}\b/g,
  ];

  return patterns.reduce((result, pattern) => result.replace(pattern, '[REDACTED]'), text);
};

/**
 * テキストがRedact必須かどうかをチェック
 */
export const requiresRedact = (sensitivity: SensitivityLevel): boolean =>
  sensitivity === 'confidential';

/**
 * 型ガード: RedactErrorかどうか
 */
export const isRedactError = (e: unknown): e is RedactError =>
  typeof e === 'object' && e !== null && '_tag' in e && (e as RedactError)._tag === 'RedactError';

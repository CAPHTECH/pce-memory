/**
 * @pce/embeddings コンテンツハッシュ
 * ADR-0003: キャッシュキー用SHA-256ハッシュ生成
 */

import { createHash } from "crypto";

/**
 * テキストを正規化してSHA-256ハッシュを生成
 * 正規化ルール:
 * - Unicode NFC正規化
 * - 前後の空白を除去
 * - 連続する空白を単一スペースに
 *
 * @param text ハッシュ対象テキスト
 * @returns SHA-256ハッシュ（16進数文字列）
 */
export const computeContentHash = (text: string): string => {
  const normalized = normalizeText(text);
  return createHash("sha256").update(normalized, "utf8").digest("hex");
};

/**
 * テキスト正規化
 * - Unicode NFC正規化（合成形式）
 * - 前後の空白を除去
 * - 連続する空白を単一スペースに
 * - 改行を統一（\r\n → \n）
 */
export const normalizeText = (text: string): string =>
  text
    .normalize("NFC")
    .replace(/\r\n/g, "\n")
    .trim()
    .replace(/\s+/g, " ");

/**
 * ハッシュが有効な形式かチェック
 * @param hash チェック対象の文字列
 * @returns 64文字の16進数文字列ならtrue
 */
export const isValidHash = (hash: string): boolean =>
  /^[a-f0-9]{64}$/i.test(hash);

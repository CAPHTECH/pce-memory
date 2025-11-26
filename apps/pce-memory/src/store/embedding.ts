/**
 * 埋め込みキャッシュストア（DuckDB永続化）
 * ADR-0003: TLA+ Inv_CacheVersionConsistency準拠
 *
 * pce-memory統合: インメモリキャッシュとDuckDB永続化を組み合わせ
 */

import * as TE from "fp-ts/TaskEither";
import { pipe } from "fp-ts/function";
import { getConnection } from "../db/connection.js";
import type { EmbeddingCache, CacheEntry } from "@pce/embeddings";
import type { CacheError } from "@pce/embeddings";
import { cacheReadError, cacheWriteError, CACHE_TTL_MS } from "@pce/embeddings";

/**
 * DuckDB永続化キャッシュ設定
 */
export interface DuckDBCacheConfig {
  /** 初期モデルバージョン */
  readonly initialModelVersion: string;
  /** TTL（ミリ秒）。デフォルト: 24時間 */
  readonly ttlMs?: number;
}

/**
 * DuckDB永続化キャッシュを作成
 *
 * TLA+ Inv_CacheVersionConsistency:
 * - キー: text_hash + model_version
 * - バージョン変更時は古いエントリは自然にマッチしなくなる
 *
 * @param config キャッシュ設定
 * @returns EmbeddingCacheインスタンス
 */
export const createDuckDBCache = (config: DuckDBCacheConfig): EmbeddingCache => {
  let currentModelVersion = config.initialModelVersion;
  const ttlMs = config.ttlMs ?? CACHE_TTL_MS;

  /**
   * TTL期限切れチェック
   */
  const isExpired = (createdAt: Date): boolean =>
    Date.now() - createdAt.getTime() > ttlMs;

  return {
    get currentModelVersion() {
      return currentModelVersion;
    },

    get: (textHash: string): TE.TaskEither<CacheError, CacheEntry | undefined> =>
      pipe(
        TE.tryCatch(
          async () => {
            const conn = await getConnection();
            const reader = await conn.runAndReadAll(
              `SELECT embedding, model_version, created_at
               FROM embedding_cache
               WHERE text_hash = $1 AND model_version = $2`,
              [textHash, currentModelVersion]
            );
            const rows = reader.getRowObjects() as unknown as {
              embedding: number[];
              model_version: string;
              created_at: Date;
            }[];

            if (rows.length === 0 || !rows[0]) {
              return undefined;
            }

            const row = rows[0];
            const createdAt = row.created_at;

            // TTL期限切れチェック
            if (isExpired(createdAt)) {
              // 期限切れエントリを削除
              await conn.run(
                `DELETE FROM embedding_cache
                 WHERE text_hash = $1 AND model_version = $2`,
                [textHash, currentModelVersion]
              );
              return undefined;
            }

            // ディープコピーを返却（ミューテーション汚染防止）
            return {
              embedding: [...row.embedding],
              modelVersion: row.model_version,
              createdAt: createdAt.getTime(),
            };
          },
          (e) => cacheReadError(e)
        )
      ),

    set: (
      textHash: string,
      embedding: readonly number[]
    ): TE.TaskEither<CacheError, void> =>
      pipe(
        TE.tryCatch(
          async () => {
            const conn = await getConnection();
            // DuckDBのINSERT OR REPLACEを使用
            // 配列はJSON文字列として渡し、SQL内でパース
            const embeddingJson = JSON.stringify([...embedding]);
            await conn.run(
              `INSERT OR REPLACE INTO embedding_cache
               (text_hash, model_version, embedding, created_at)
               VALUES ($1, $2, $3::DOUBLE[], CURRENT_TIMESTAMP)`,
              [textHash, currentModelVersion, embeddingJson]
            );
          },
          (e) => cacheWriteError(e)
        )
      ),

    invalidateAll: (): TE.TaskEither<CacheError, void> =>
      pipe(
        TE.tryCatch(
          async () => {
            const conn = await getConnection();
            // 現在のバージョンのエントリのみ削除（他バージョンは残す）
            await conn.run(
              `DELETE FROM embedding_cache WHERE model_version = $1`,
              [currentModelVersion]
            );
          },
          (e) => cacheWriteError(e)
        )
      ),

    updateModelVersion: (newVersion: string): TE.TaskEither<CacheError, void> =>
      pipe(
        TE.tryCatch(
          async () => {
            if (newVersion !== currentModelVersion) {
              // 古いバージョンのエントリを削除（オプショナル）
              // バージョン込みキー戦略により自動的にマッチしなくなるが、
              // ストレージ節約のため削除
              const conn = await getConnection();
              await conn.run(
                `DELETE FROM embedding_cache WHERE model_version = $1`,
                [currentModelVersion]
              );
              currentModelVersion = newVersion;
            }
          },
          (e) => cacheWriteError(e)
        )
      ),

    invalidateByModelVersion: (version: string): TE.TaskEither<CacheError, void> =>
      pipe(
        TE.tryCatch(
          async () => {
            const conn = await getConnection();
            await conn.run(
              `DELETE FROM embedding_cache WHERE model_version = $1`,
              [version]
            );
          },
          (e) => cacheWriteError(e)
        )
      ),
  };
};

/**
 * キャッシュ統計情報を取得
 */
export interface CacheDBStats {
  /** 現在のモデルバージョンのエントリ数 */
  readonly currentVersionCount: number;
  /** 全エントリ数 */
  readonly totalCount: number;
  /** 現在のモデルバージョン */
  readonly modelVersion: string;
}

export const getDuckDBCacheStats = async (
  cache: EmbeddingCache
): Promise<CacheDBStats> => {
  const conn = await getConnection();

  const currentReader = await conn.runAndReadAll(
    `SELECT COUNT(*) as cnt FROM embedding_cache WHERE model_version = $1`,
    [cache.currentModelVersion]
  );
  const currentRows = currentReader.getRowObjects() as unknown as {
    cnt: number | bigint;
  }[];

  const totalReader = await conn.runAndReadAll(
    `SELECT COUNT(*) as cnt FROM embedding_cache`
  );
  const totalRows = totalReader.getRowObjects() as unknown as {
    cnt: number | bigint;
  }[];

  return {
    currentVersionCount: currentRows[0] ? Number(currentRows[0].cnt) : 0,
    totalCount: totalRows[0] ? Number(totalRows[0].cnt) : 0,
    modelVersion: cache.currentModelVersion,
  };
};

/**
 * 期限切れエントリをクリーンアップ
 * （定期的なメンテナンスタスク用）
 */
export const cleanupExpiredEntries = async (ttlMs = CACHE_TTL_MS): Promise<number> => {
  const conn = await getConnection();
  const cutoffMs = Date.now() - ttlMs;

  // DuckDBのTIMESTAMPはISO文字列で比較
  const result = await conn.runAndReadAll(
    `DELETE FROM embedding_cache
     WHERE created_at < epoch_ms($1)::TIMESTAMP
     RETURNING text_hash`,
    [cutoffMs]
  );
  const rows = result.getRowObjects();
  return rows.length;
};

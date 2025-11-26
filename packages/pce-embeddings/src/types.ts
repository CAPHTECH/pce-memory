/**
 * @pce/embeddings 型定義
 * ADR-0003/TLA+ pce_embedding.tla仕様に準拠
 */

import * as TE from "fp-ts/TaskEither";
import type { EmbeddingError, CacheError } from "./errors.js";

// ========== TLA+ CONSTANTS ==========

/** TLA+: ProviderStatus == {"available", "unavailable", "degraded"} */
export type ProviderStatus = "available" | "unavailable" | "degraded";

/** Alloy: SensitivityLevel -> Public, Internal, Confidential */
export type SensitivityLevel = "public" | "internal" | "confidential";

/** ADR-0003: バッチサイズ上限 */
export const MAX_BATCH_SIZE = 32;

/** ADR-0003: キャッシュTTL（24時間） */
export const CACHE_TTL_MS = 24 * 60 * 60 * 1000;

/** ADR-0003: デフォルト次元数（all-MiniLM-L6-v2） */
export const DEFAULT_DIMENSIONS = 384;

// ========== TLA+ CacheEntry ==========

/**
 * TLA+: CacheEntry == [vector: Vector, modelVersion: ModelVersion]
 * キャッシュエントリ（バージョン込みキー戦略に対応）
 */
export interface CacheEntry {
  /** 埋め込みベクトル（384次元） */
  readonly embedding: readonly number[];
  /** モデルバージョン（Inv_CacheVersionConsistency用） */
  readonly modelVersion: string;
  /** 作成時刻（UNIX epoch ms） */
  readonly createdAt: number;
}

// ========== EmbeddingProvider Interface ==========

/**
 * TLA+: ProviderRec == [status: ProviderStatus, modelVersion: ModelVersion]
 * 埋め込みプロバイダーインターフェース
 */
export interface EmbeddingProvider {
  /** モデルバージョン（例: "all-MiniLM-L6-v2"） */
  readonly modelVersion: string;
  /** プロバイダー状態 */
  readonly status: ProviderStatus;

  /**
   * 単一テキストの埋め込み生成
   * TLA+: StartProcessing + CompleteProcessing
   */
  embed(text: string): TE.TaskEither<EmbeddingError, readonly number[]>;

  /**
   * バッチ埋め込み生成（最大32件）
   * ADR-0003: MaxBatchSize = 32
   */
  embedBatch(texts: readonly string[]): TE.TaskEither<EmbeddingError, readonly (readonly number[])[]>;
}

// ========== EmbeddingCache Interface ==========

/**
 * Alloy: sig CacheState
 * TLA+: Inv_CacheVersionConsistency準拠キャッシュインターフェース
 */
export interface EmbeddingCache {
  /** 現在のモデルバージョン */
  readonly currentModelVersion: string;

  /**
   * キャッシュ検索
   * TLA+: ProcessCacheHit
   * @param textHash SHA-256ハッシュ
   */
  get(textHash: string): TE.TaskEither<CacheError, CacheEntry | undefined>;

  /**
   * キャッシュ保存
   * TLA+: CompleteProcessing後のキャッシュ更新
   * @param textHash SHA-256ハッシュ
   * @param embedding 埋め込みベクトル
   * @param modelVersion 埋め込み生成に使用したモデルバージョン（型安全なバージョン追跡）
   */
  set(textHash: string, embedding: readonly number[], modelVersion: string): TE.TaskEither<CacheError, void>;

  /**
   * 全エントリ無効化
   * TLA+: UpdateModelVersion時に呼び出し
   */
  invalidateAll(): TE.TaskEither<CacheError, void>;

  /**
   * モデルバージョン更新（全キャッシュ無効化を伴う）
   * TLA+: UpdateModelVersion action
   */
  updateModelVersion(newVersion: string): TE.TaskEither<CacheError, void>;

  /**
   * 指定バージョンのエントリを無効化
   * ADR-0003: バージョン指定の無効化
   * @param version 無効化するモデルバージョン
   */
  invalidateByModelVersion(version: string): TE.TaskEither<CacheError, void>;
}

// ========== Service Types ==========

/**
 * 埋め込みリクエストパラメータ
 * Alloy: sig EmbeddingRequest
 */
export interface EmbedParams {
  /** 埋め込み対象テキスト */
  readonly text: string;
  /** 機密レベル（Alloy RedactBeforeEmbed用） */
  readonly sensitivity: SensitivityLevel;
  /** キャッシュをスキップするか */
  readonly skipCache?: boolean;
}

/**
 * 埋め込み結果
 * TLA+: CompletedRec対応
 */
export interface EmbedResult {
  /** 埋め込みベクトル */
  readonly embedding: readonly number[];
  /** 使用されたモデルバージョン */
  readonly modelVersion: string;
  /** キャッシュからの取得か */
  readonly fromCache: boolean;
  /** テキストハッシュ（デバッグ用） */
  readonly textHash: string;
}

/**
 * バッチ埋め込み結果
 */
export interface BatchEmbedResult {
  /** 各テキストの埋め込み結果 */
  readonly results: readonly EmbedResult[];
  /** 処理されたテキスト数 */
  readonly processedCount: number;
  /** キャッシュヒット数 */
  readonly cacheHits: number;
}

// ========== Provider Configuration ==========

/**
 * ローカルプロバイダー設定（基本型）
 * ADR-0003: LocalEmbeddingProvider
 * Note: providers/local.ts の LocalProviderConfig は @xenova/transformers 用に拡張
 */
export interface LocalProviderConfigBase {
  /** モデルバージョン識別子 */
  readonly modelVersion?: string;
  /** キャッシュディレクトリ */
  readonly cacheDir?: string;
}

/**
 * リモートプロバイダー設定
 * ADR-0003: RemoteEmbeddingProvider
 */
export interface RemoteProviderConfig {
  /** APIエンドポイント */
  readonly endpoint: string;
  /** APIキー */
  readonly apiKey: string;
  /** モデル名 */
  readonly model: string;
}

/**
 * EmbeddingService設定
 */
export interface EmbeddingServiceConfig {
  /** プライマリプロバイダー */
  readonly primary: EmbeddingProvider;
  /** フォールバックプロバイダー（オプション） */
  readonly fallback?: EmbeddingProvider;
  /** キャッシュ */
  readonly cache: EmbeddingCache;
  /**
   * キャッシュエラー時のコールバック（オブザーバビリティ用）
   * ベストエフォートキャッシュのため、エラーは致命的にならない
   * @param error キャッシュエラー
   * @param operation 'read' | 'write'
   */
  readonly onCacheError?: (error: CacheError, operation: 'read' | 'write') => void;
}

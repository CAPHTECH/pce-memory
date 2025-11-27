/**
 * Hybrid Search実装（ADR-0004 設計C準拠）
 *
 * TLA+ 不変条件対応:
 * - Inv_C_ScopeConsistency: WHERE scope IN (...) でスコープフィルタ
 * - Inv_C_ThresholdFiltering: WHERE score >= THRESHOLD でフィルタ
 * - Inv_C_MergeComplete: Promise.all + union merge で両検索結果統合
 * - Inv_C_FusionCorrectness: hybrid_score(text, vec, α) で融合
 *
 * パラメータ（ADR-0004より）:
 * - α (ALPHA) = 0.65: ベクトル重視
 * - THRESHOLD = 0.15: 低ノイズフィルタ
 * - k_text = 48: テキスト検索上限
 * - k_vec = 96: ベクトル検索上限
 *
 * @see docs/adr/0004-hybrid-search-design.md
 * @see docs/spec/tlaplus/hybrid_search_simple.tla
 */

import { getConnection } from "../db/connection.js";
import type { Claim } from "./claims.js";
import type { EmbeddingService } from "@pce/embeddings";
import * as E from "fp-ts/Either";
import {
  calculateGFromClaim,
  type GFactorBreakdown,
  type ScoreBreakdown,
} from "./rerank.js";
import { normalizeRowsTimestamps } from "../utils/serialization.js";

// ========== ADR-0004 パラメータ ==========

/** ベクトル検索重み（TLA+ Alpha = 65 / 100） */
const ALPHA = 0.65;

/** 採用閾値（TLA+ Threshold = 15 / 100） */
const THRESHOLD = 0.15;

/** テキスト検索上限（3× of k_final） */
const K_TEXT = 48;

/** ベクトル検索上限（6× of k_final） */
const K_VEC = 96;

/** criticスコアが存在しない場合のデフォルト値 */
const DEFAULT_CRITIC_SCORE = 0.5;

/** 最小limit値 */
const MIN_LIMIT = 1;

/** 埋め込み次元数の上限（一般的なモデルの最大値） */
const MAX_EMBEDDING_DIM = 4096;

/** 埋め込み値の絶対値上限（正規化ベクトルは通常[-1, 1]範囲） */
const MAX_EMBEDDING_MAGNITUDE = 10.0;

// ========== ユーティリティ関数 ==========

/**
 * 埋め込みベクトルが有効か検証
 * - 空ベクトル禁止
 * - 次元数上限チェック（DoS防止）
 * - 各値の有限性チェック（NaN/Infinity禁止）
 * - 各値の絶対値上限チェック（異常値検出）
 *
 * @param embedding 検証対象のベクトル
 * @throws Error 不正な値が含まれる場合
 */
function validateEmbedding(embedding: readonly number[]): void {
  if (embedding.length === 0) {
    throw new Error("Embedding vector must not be empty");
  }
  if (embedding.length > MAX_EMBEDDING_DIM) {
    throw new Error(
      `Embedding dimension ${embedding.length} exceeds maximum ${MAX_EMBEDDING_DIM}`
    );
  }
  for (let i = 0; i < embedding.length; i++) {
    const v = embedding[i];
    if (typeof v !== "number" || !Number.isFinite(v)) {
      throw new Error(`Invalid embedding value at index ${i}: ${v}`);
    }
    if (Math.abs(v) > MAX_EMBEDDING_MAGNITUDE) {
      throw new Error(
        `Embedding value ${v} at index ${i} exceeds magnitude limit ${MAX_EMBEDDING_MAGNITUDE}`
      );
    }
  }
}

/**
 * LIKEパターンの特殊文字をエスケープ
 * @param query 検索クエリ
 * @returns エスケープ済みクエリ
 */
function escapeLikePattern(query: string): string {
  // DuckDBのLIKE: % と _ が特殊文字
  return query.replace(/[%_\\]/g, "\\$&");
}

/**
 * limit値を正規化（最小値保証）
 * @param limit 元のlimit値
 * @returns 正規化されたlimit値
 */
function normalizeLimit(limit: number): number {
  return Math.max(MIN_LIMIT, Math.floor(limit));
}

// ========== 型定義 ==========

/**
 * 検索結果（スコア付き）
 * TLA+: [claim: ClaimId, score: Score]
 */
interface SearchResult {
  claim: Claim;
  score: number;
}

/**
 * g()再ランキング用メトリクス
 */
interface ClaimMetrics {
  id: string;
  utility: number;
  confidence: number;
  /** 有効タイムスタンプ（updated_at or created_at） */
  ts_eff: Date | string;
  kind: string;
}

/**
 * utility統計情報（z-score計算用）
 */
interface UtilityStats {
  mean: number;
  std: number;
}

/**
 * g()適用済み検索結果
 */
export interface RankedSearchResult {
  claim: Claim;
  fusedScore: number;
  breakdown?: ScoreBreakdown;
}

/**
 * Hybrid Search設定
 */
export interface HybridSearchConfig {
  /** EmbeddingService（クエリ埋め込み生成用） */
  embeddingService: EmbeddingService;
  /** α係数（オプション、デフォルト0.65） */
  alpha?: number;
  /** 閾値（オプション、デフォルト0.15） */
  threshold?: number;
  /** g()再ランキングを有効化（オプション、デフォルトtrue） */
  enableRerank?: boolean;
  /** デバッグ用: スコア内訳を含める（オプション、デフォルトfalse） */
  includeBreakdown?: boolean;
  /** カーソル（ページネーション用、claim_idを使用） */
  cursor?: string;
}

/**
 * スコア付きClaim（検索結果用）
 */
export interface ScoredClaim {
  claim: Claim;
  /** 融合スコア（g()適用後） */
  score: number;
}

/**
 * ページネーション付き検索結果
 * exactOptionalPropertyTypes対応: next_cursorはundefinedも許容
 */
export interface PaginatedSearchResult {
  /** スコア付きClaim配列 */
  results: ScoredClaim[];
  /** 次ページのカーソル（最後のclaim_id、ない場合はundefined）*/
  next_cursor: string | undefined;
  /** さらに結果があるか */
  has_more: boolean;
  /** 総件数（概算、limitまでの取得数） */
  total_in_page: number;
}

// ========== グローバル設定 ==========

/** グローバルEmbeddingService（index.tsから初期化） */
let globalEmbeddingService: EmbeddingService | null = null;

/**
 * EmbeddingServiceを設定
 * MCP server初期化時に呼び出す
 */
export function setEmbeddingService(service: EmbeddingService): void {
  globalEmbeddingService = service;
}

/**
 * EmbeddingServiceを取得
 */
export function getEmbeddingService(): EmbeddingService | null {
  return globalEmbeddingService;
}

// ========== Text検索 ==========

/**
 * テキスト検索（ILIKE）
 * TLA+ C_TextSearch: スコープ内のテキスト一致候補を取得
 *
 * @param query 検索クエリ文字列
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @returns スコア付き検索結果
 */
export async function textSearch(
  query: string,
  scopes: string[],
  limit: number = K_TEXT
): Promise<SearchResult[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const normalizedLimit = normalizeLimit(limit);

  // スコープのプレースホルダー構築
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(",");
  // LIKEパターンの特殊文字をエスケープ
  const escapedQuery = escapeLikePattern(query);
  const queryParam = `%${escapedQuery}%`;

  // criticスコアとテキストマッチを組み合わせたスコア計算
  // TLA+ claimTextRelevant: LIKE '%query%' で判定
  const sql = `
    SELECT
      c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash,
      c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
      COALESCE(cr.score, ${DEFAULT_CRITIC_SCORE}) as text_score
    FROM claims c
    LEFT JOIN critic cr ON cr.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
      AND c.text ILIKE $${scopes.length + 1} ESCAPE '\\'
    ORDER BY text_score DESC
    LIMIT $${scopes.length + 2}
  `;

  const reader = await conn.runAndReadAll(sql, [...scopes, queryParam, normalizedLimit]);
  const rawRows = reader.getRowObjects() as unknown as (Claim & { text_score: number })[];
  const rows = normalizeRowsTimestamps(rawRows);

  return rows.map((row) => ({
    claim: {
      id: row.id,
      text: row.text,
      kind: row.kind,
      scope: row.scope,
      boundary_class: row.boundary_class,
      content_hash: row.content_hash,
      utility: row.utility,
      confidence: row.confidence,
      created_at: row.created_at,
      updated_at: row.updated_at,
      recency_anchor: row.recency_anchor,
    },
    score: row.text_score,
  }));
}

// ========== Vector検索 ==========

/**
 * ベクトル検索（cos_sim）
 * TLA+ C_VecSearch: スコープ内のベクトル類似候補を取得
 *
 * @param queryEmbedding クエリの埋め込みベクトル
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @returns スコア付き検索結果
 */
export async function vectorSearch(
  queryEmbedding: readonly number[],
  scopes: string[],
  limit: number = K_VEC
): Promise<SearchResult[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  // 埋め込みベクトルの検証
  validateEmbedding(queryEmbedding);

  const conn = await getConnection();
  const normalizedLimit = normalizeLimit(limit);

  // claim_vectorsが空の場合は空配列を返す
  const countReader = await conn.runAndReadAll("SELECT COUNT(*) as cnt FROM claim_vectors");
  const countRows = countReader.getRowObjects() as unknown as { cnt: number | bigint }[];
  if (!countRows[0] || Number(countRows[0].cnt) === 0) {
    return [];
  }

  // スコープのプレースホルダー構築
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(",");

  // DuckDB Node APIは配列パラメータを直接サポートしないため、
  // 配列リテラル文字列として埋め込む（検証済みなので安全）
  const embeddingLiteral = `[${[...queryEmbedding].join(",")}]`;

  // cos_simマクロでベクトル類似度計算
  // TLA+ claimVecRelevant: cos_sim >= threshold で判定
  // norm_cosで[-1,1]を[0,1]に正規化
  const sql = `
    SELECT
      c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash,
      c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
      norm_cos(cos_sim(cv.embedding, ${embeddingLiteral}::DOUBLE[])) as vec_score
    FROM claims c
    INNER JOIN claim_vectors cv ON cv.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
    ORDER BY vec_score DESC
    LIMIT $${scopes.length + 1}
  `;

  const reader = await conn.runAndReadAll(sql, [...scopes, normalizedLimit]);
  const rawRows = reader.getRowObjects() as unknown as (Claim & { vec_score: number })[];
  const rows = normalizeRowsTimestamps(rawRows);

  return rows.map((row) => ({
    claim: {
      id: row.id,
      text: row.text,
      kind: row.kind,
      scope: row.scope,
      boundary_class: row.boundary_class,
      content_hash: row.content_hash,
      utility: row.utility,
      confidence: row.confidence,
      created_at: row.created_at,
      updated_at: row.updated_at,
      recency_anchor: row.recency_anchor,
    },
    score: row.vec_score,
  }));
}

// ========== 結果マージ ==========

/**
 * テキストとベクトル検索結果をマージ
 * TLA+ C_Merge: FULL OUTER JOIN相当
 *
 * @param textResults テキスト検索結果
 * @param vecResults ベクトル検索結果
 * @param alpha ベクトル重み
 * @param threshold 閾値
 * @returns 融合スコア付きClaim配列
 */
function mergeResults(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  alpha: number,
  threshold: number
): { claim: Claim; fusedScore: number }[] {
  // ClaimIdでマップ化
  const textMap = new Map<string, SearchResult>();
  for (const r of textResults) {
    textMap.set(r.claim.id, r);
  }

  const vecMap = new Map<string, SearchResult>();
  for (const r of vecResults) {
    vecMap.set(r.claim.id, r);
  }

  // 全候補のIDを収集（UNION）
  // TLA+ Inv_C_MergeComplete: C_merged = C_textCandidates ∪ C_vecCandidates
  const allIds = new Set([...textMap.keys(), ...vecMap.keys()]);

  const merged: { claim: Claim; fusedScore: number }[] = [];

  for (const id of allIds) {
    const textResult = textMap.get(id);
    const vecResult = vecMap.get(id);

    // 少なくとも一方には存在（UNIONなので）
    const claim = textResult?.claim ?? vecResult?.claim;
    if (!claim) continue;

    // スコア取得（存在しない方は0）
    const textScore = textResult?.score ?? 0;
    const vecScore = vecResult?.score ?? 0;

    // TLA+ FusedScore: α × vecScore + (1-α) × textScore
    const fusedScore = alpha * vecScore + (1 - alpha) * textScore;

    // TLA+ Inv_C_ThresholdFiltering: score >= threshold
    if (fusedScore >= threshold) {
      merged.push({ claim, fusedScore });
    }
  }

  // スコア降順ソート
  merged.sort((a, b) => b.fusedScore - a.fusedScore);

  return merged;
}

// ========== g()再ランキング用ヘルパー ==========

/**
 * utility統計情報を取得（z-score計算用）
 * @param scopes 検索対象スコープ
 * @returns mean, std（stdが0の場合は1.0を返す）
 */
async function getClaimStats(scopes: string[]): Promise<UtilityStats> {
  if (scopes.length === 0) {
    return { mean: 0, std: 1 };
  }

  const conn = await getConnection();
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(",");

  const sql = `
    SELECT
      AVG(utility) as mean,
      COALESCE(NULLIF(STDDEV_SAMP(utility), 0), 1.0) as std
    FROM claims
    WHERE scope IN (${scopePlaceholders})
  `;

  const reader = await conn.runAndReadAll(sql, scopes);
  const rows = reader.getRowObjects() as unknown as { mean: number | null; std: number }[];
  const row = rows[0];

  if (!row || row.mean === null) {
    return { mean: 0, std: 1 };
  }

  return { mean: row.mean, std: row.std };
}

/**
 * Claimメトリクスを取得
 * @param claimIds 取得対象のClaim ID配列
 * @returns ClaimIdをキーとするメトリクスマップ
 */
async function fetchClaimMetrics(claimIds: string[]): Promise<Map<string, ClaimMetrics>> {
  if (claimIds.length === 0) {
    return new Map();
  }

  const conn = await getConnection();
  const placeholders = claimIds.map((_, i) => `$${i + 1}`).join(",");

  // recency計算にはrecency_anchorを使用（positive feedbackでのみ更新される）
  const sql = `
    SELECT
      id, utility, confidence, kind,
      COALESCE(recency_anchor, created_at) as ts_eff
    FROM claims
    WHERE id IN (${placeholders})
  `;

  const reader = await conn.runAndReadAll(sql, claimIds);
  const rawRows = reader.getRowObjects() as unknown as ClaimMetrics[];
  const rows = normalizeRowsTimestamps(rawRows);

  const metricsMap = new Map<string, ClaimMetrics>();
  for (const row of rows) {
    metricsMap.set(row.id, row);
  }

  return metricsMap;
}

/**
 * g()適用版マージ関数
 * TLA+ Inv_RangeBounds: g ∈ [0.09, 1.0]
 *
 * @param textResults テキスト検索結果
 * @param vecResults ベクトル検索結果
 * @param claimMetrics Claimメトリクスマップ
 * @param stats utility統計情報
 * @param alpha ベクトル重み
 * @param threshold 閾値
 * @param includeBreakdown スコア内訳を含めるか
 * @returns g()適用済み検索結果
 */
function mergeResultsWithRerank(
  textResults: SearchResult[],
  vecResults: SearchResult[],
  claimMetrics: Map<string, ClaimMetrics>,
  stats: UtilityStats,
  alpha: number,
  threshold: number,
  includeBreakdown: boolean = false
): RankedSearchResult[] {
  // ClaimIdでマップ化
  const textMap = new Map<string, SearchResult>();
  for (const r of textResults) {
    textMap.set(r.claim.id, r);
  }

  const vecMap = new Map<string, SearchResult>();
  for (const r of vecResults) {
    vecMap.set(r.claim.id, r);
  }

  // 全候補のIDを収集（UNION）
  const allIds = new Set([...textMap.keys(), ...vecMap.keys()]);

  const merged: RankedSearchResult[] = [];

  for (const id of allIds) {
    const textResult = textMap.get(id);
    const vecResult = vecMap.get(id);

    const claim = textResult?.claim ?? vecResult?.claim;
    if (!claim) continue;

    // スコア取得
    const textScore = textResult?.score ?? 0;
    const vecScore = vecResult?.score ?? 0;

    // 融合スコア S = α × vecScore + (1-α) × textScore
    const S = alpha * vecScore + (1 - alpha) * textScore;

    // メトリクス取得（存在しない場合はデフォルト値）
    const metrics = claimMetrics.get(id);
    let gFactor: GFactorBreakdown;

    if (metrics) {
      gFactor = calculateGFromClaim(
        metrics.utility,
        metrics.confidence,
        metrics.ts_eff,
        metrics.kind,
        stats
      );
    } else {
      // メトリクスがない場合: g = 1.0（影響なし）
      gFactor = {
        utility_term: 1.0,
        confidence_term: 1.0,
        recency_term: 1.0,
        g: 1.0,
      };
    }

    // 最終スコア: score_final = S × g
    const scoreFinal = S * gFactor.g;

    // 閾値フィルタ
    if (scoreFinal >= threshold) {
      const result: RankedSearchResult = { claim, fusedScore: scoreFinal };

      if (includeBreakdown) {
        result.breakdown = {
          s_text: textScore,
          s_vec: vecScore,
          S,
          g: gFactor,
          score_final: scoreFinal,
        };
      }

      merged.push(result);
    }
  }

  // スコア降順ソート
  merged.sort((a, b) => b.fusedScore - a.fusedScore);

  return merged;
}

// ========== Hybrid Search メイン ==========

/**
 * ハイブリッド検索
 * ADR-0004 設計C: テキスト+ベクトル融合検索
 *
 * 処理フロー:
 * 1. クエリ埋め込み生成（失敗時: Text-onlyフォールバック）
 * 2. 並列検索: Promise.all([textSearch, vectorSearch])
 * 3. 結果マージ: FULL OUTER JOIN
 * 4. スコア融合: hybrid_score(text, vec, α)
 * 5. 閾値フィルタ: score >= 0.15
 * 6. ランキング: ORDER BY score DESC LIMIT k
 *
 * TLA+ 活性性質:
 * - Liveness_EventuallyDone: async/awaitで完了保証
 * - Liveness_C_MergeEventuallyComplete: Promise.all()で並列実行
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（オプション）
 * @returns Claim配列
 */
export async function hybridSearch(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<Claim[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  const normalizedLimit = normalizeLimit(limit);
  const alpha = config?.alpha ?? ALPHA;
  const threshold = config?.threshold ?? THRESHOLD;
  const embeddingService = config?.embeddingService ?? globalEmbeddingService;

  // クエリがない場合はcriticスコアで取得（既存動作）
  if (!query || query.trim().length === 0) {
    return fallbackToTextOnly(scopes, normalizedLimit);
  }

  // Step 1: クエリ埋め込み生成
  let queryEmbedding: readonly number[] | null = null;

  if (embeddingService) {
    const embedResult = await embeddingService.embed({
      text: query,
      sensitivity: "internal",
    })();

    if (E.isRight(embedResult)) {
      queryEmbedding = embedResult.right.embedding;
    }
    // 失敗時はText-onlyフォールバック（queryEmbedding = null）
  }

  const enableRerank = config?.enableRerank ?? true;
  const includeBreakdown = config?.includeBreakdown ?? false;

  // Step 2: 並列検索実行
  // TLA+ Liveness_C_MergeEventuallyComplete: Promise.all()
  if (queryEmbedding) {
    const [textResults, vecResults] = await Promise.all([
      textSearch(query, scopes, K_TEXT),
      vectorSearch(queryEmbedding, scopes, K_VEC),
    ]);

    // Step 3-5: マージ + 融合 + フィルタ + ソート（g()再ランキング対応）
    let merged: { claim: Claim; fusedScore: number }[];

    if (enableRerank) {
      // g()再ランキング有効: utility/confidence/recencyを考慮
      const allClaimIds = [
        ...textResults.map((r) => r.claim.id),
        ...vecResults.map((r) => r.claim.id),
      ];
      const uniqueIds = [...new Set(allClaimIds)];

      // 並列でstatsとmetricsを取得
      const [stats, claimMetrics] = await Promise.all([
        getClaimStats(scopes),
        fetchClaimMetrics(uniqueIds),
      ]);

      merged = mergeResultsWithRerank(
        textResults,
        vecResults,
        claimMetrics,
        stats,
        alpha,
        threshold,
        includeBreakdown
      );
    } else {
      // g()再ランキング無効: 従来の融合スコアのみ
      merged = mergeResults(textResults, vecResults, alpha, threshold);
    }

    // Step 6: 上位k件を返却
    return merged.slice(0, normalizedLimit).map((r) => r.claim);
  }

  // Text-onlyフォールバック（埋め込み生成失敗時）
  const textResults = await textSearch(query, scopes, normalizedLimit);
  return textResults
    .filter((r) => r.score >= threshold)
    .slice(0, normalizedLimit)
    .map((r) => r.claim);
}

/**
 * スコア付きハイブリッド検索
 * hybridSearchと同じロジックだが、fusedScoreも返す
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（オプション）
 * @returns ScoredClaim配列（claim + score）
 */
export async function hybridSearchWithScores(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<ScoredClaim[]> {
  // 空scopesの早期リターン
  if (scopes.length === 0) {
    return [];
  }

  const normalizedLimit = normalizeLimit(limit);
  const alpha = config?.alpha ?? ALPHA;
  const threshold = config?.threshold ?? THRESHOLD;
  const embeddingService = config?.embeddingService ?? globalEmbeddingService;

  // クエリがない場合はcriticスコアで取得（既存動作）
  if (!query || query.trim().length === 0) {
    const claims = await fallbackToTextOnly(scopes, normalizedLimit);
    // フォールバック時はcriticスコアを使用（0.5をデフォルト）
    return claims.map((claim, index) => ({
      claim,
      score: Math.max(0.1, 1.0 - index * 0.05), // 順位ベースの近似スコア
    }));
  }

  // Step 1: クエリ埋め込み生成
  let queryEmbedding: readonly number[] | null = null;

  if (embeddingService) {
    const embedResult = await embeddingService.embed({
      text: query,
      sensitivity: "internal",
    })();

    if (E.isRight(embedResult)) {
      queryEmbedding = embedResult.right.embedding;
    }
  }

  const enableRerank = config?.enableRerank ?? true;
  const includeBreakdown = config?.includeBreakdown ?? false;

  // Step 2: 並列検索実行
  if (queryEmbedding) {
    const [textResults, vecResults] = await Promise.all([
      textSearch(query, scopes, K_TEXT),
      vectorSearch(queryEmbedding, scopes, K_VEC),
    ]);

    // Step 3-5: マージ + 融合 + フィルタ + ソート
    let merged: { claim: Claim; fusedScore: number }[];

    if (enableRerank) {
      const allClaimIds = [
        ...textResults.map((r) => r.claim.id),
        ...vecResults.map((r) => r.claim.id),
      ];
      const uniqueIds = [...new Set(allClaimIds)];

      const [stats, claimMetrics] = await Promise.all([
        getClaimStats(scopes),
        fetchClaimMetrics(uniqueIds),
      ]);

      merged = mergeResultsWithRerank(
        textResults,
        vecResults,
        claimMetrics,
        stats,
        alpha,
        threshold,
        includeBreakdown
      );
    } else {
      merged = mergeResults(textResults, vecResults, alpha, threshold);
    }

    // Step 6: 上位k件を返却（スコア付き）
    return merged.slice(0, normalizedLimit).map((r) => ({
      claim: r.claim,
      score: r.fusedScore,
    }));
  }

  // Text-onlyフォールバック
  const textResults = await textSearch(query, scopes, normalizedLimit);
  return textResults
    .filter((r) => r.score >= threshold)
    .slice(0, normalizedLimit)
    .map((r) => ({
      claim: r.claim,
      score: r.score,
    }));
}

/**
 * ページネーション付きハイブリッド検索
 * mcp-tools.md §2.1, §2.2 cursor/next_cursor/has_more対応
 * 実際のfusedScoreを返す改善版
 *
 * @param scopes 検索対象スコープ配列
 * @param limit 結果上限
 * @param query 検索クエリ（オプション）
 * @param config 設定（cursor含む）
 * @returns ページネーション付き結果（スコア付き）
 */
export async function hybridSearchPaginated(
  scopes: string[],
  limit: number,
  query?: string,
  config?: Partial<HybridSearchConfig>
): Promise<PaginatedSearchResult> {
  const cursor = config?.cursor;

  // カーソル指定時はlimit+1件取得してhas_moreを判定
  const fetchLimit = limit + 1;

  // スコア付き検索を呼び出し（limit+1件取得）
  const allResults = await hybridSearchWithScores(scopes, fetchLimit, query, {
    ...config,
    // cursorは内部で処理しないので除外
  });

  // カーソル以降のデータをフィルタ
  let filteredResults = allResults;
  if (cursor) {
    const cursorIndex = allResults.findIndex((r) => r.claim.id === cursor);
    if (cursorIndex >= 0) {
      // カーソルの次から取得
      filteredResults = allResults.slice(cursorIndex + 1);
    }
  }

  // has_more判定とlimit適用
  const has_more = filteredResults.length > limit;
  const results = filteredResults.slice(0, limit);

  // 次カーソル（最後のclaim_id）
  const next_cursor = has_more && results.length > 0 ? results[results.length - 1]!.claim.id : undefined;

  return {
    results,
    next_cursor,
    has_more,
    total_in_page: results.length,
  };
}

/**
 * クエリなしの場合のフォールバック
 * criticスコアでソートして返す（既存listClaimsByScopeと同等）
 */
async function fallbackToTextOnly(scopes: string[], limit: number): Promise<Claim[]> {
  // 空scopesの早期リターン（hybridSearchで既にチェック済みだが防御的に）
  if (scopes.length === 0) {
    return [];
  }

  const conn = await getConnection();
  const scopePlaceholders = scopes.map((_, i) => `$${i + 1}`).join(",");

  const sql = `
    SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash,
           c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
           COALESCE(cr.score, 0) as score
    FROM claims c
    LEFT JOIN critic cr ON cr.claim_id = c.id
    WHERE c.scope IN (${scopePlaceholders})
    ORDER BY score DESC
    LIMIT $${scopes.length + 1}
  `;

  const reader = await conn.runAndReadAll(sql, [...scopes, limit]);
  const rawRows = reader.getRowObjects() as unknown as Claim[];
  return normalizeRowsTimestamps(rawRows);
}

// ========== claim_vectors操作 ==========

/**
 * Claimの埋め込みベクトルを保存
 *
 * @param claimId Claim ID
 * @param embedding 埋め込みベクトル
 * @param modelVersion モデルバージョン
 */
export async function saveClaimVector(
  claimId: string,
  embedding: readonly number[],
  modelVersion: string
): Promise<void> {
  // 埋め込みベクトルの検証（SQLインジェクション防止）
  validateEmbedding(embedding);

  const conn = await getConnection();
  // DuckDB Node APIは配列パラメータを直接サポートしないため、
  // 配列リテラル文字列として埋め込む（検証済みなので安全）
  const embeddingLiteral = `[${embedding.join(",")}]`;
  await conn.run(
    `INSERT INTO claim_vectors (claim_id, embedding, model_version)
     VALUES ($1, ${embeddingLiteral}::DOUBLE[], $2)
     ON CONFLICT (claim_id)
     DO UPDATE SET embedding = EXCLUDED.embedding, model_version = EXCLUDED.model_version`,
    [claimId, modelVersion]
  );
}

/**
 * Claimの埋め込みベクトルを取得
 *
 * @param claimId Claim ID
 * @returns 埋め込みベクトル（存在しない場合undefined）
 */
export async function getClaimVector(claimId: string): Promise<readonly number[] | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    "SELECT embedding FROM claim_vectors WHERE claim_id = $1",
    [claimId]
  );
  const rows = reader.getRowObjects();

  if (rows.length === 0) {
    return undefined;
  }

  const row = rows[0] as Record<string, unknown>;
  const embedding = row["embedding"];

  if (embedding == null) {
    return undefined;
  }

  // すでにnumber[]の場合
  if (Array.isArray(embedding)) {
    return embedding as number[];
  }

  // DuckDB Node APIはDOUBLE[]配列をDuckDBListValueオブジェクトとして返す
  // DuckDBListValue: { items: number[] } 形式
  if (typeof embedding === "object" && "items" in embedding) {
    const listValue = embedding as { items: number[] };
    if (Array.isArray(listValue.items)) {
      return listValue.items;
    }
  }

  // Float64Arrayの場合
  if (embedding instanceof Float64Array || ArrayBuffer.isView(embedding)) {
    return Array.from(embedding as Float64Array);
  }

  return undefined;
}

/**
 * Claimの埋め込みベクトルを削除
 *
 * @param claimId Claim ID
 */
export async function deleteClaimVector(claimId: string): Promise<void> {
  const conn = await getConnection();
  await conn.run("DELETE FROM claim_vectors WHERE claim_id = $1", [claimId]);
}

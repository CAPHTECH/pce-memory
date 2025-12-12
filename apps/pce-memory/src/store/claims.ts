import { getConnection } from '../db/connection.js';
import type { EmbeddingService } from '@pce/embeddings';
import * as E from 'fp-ts/Either';
import { saveClaimVector, splitQueryWords, buildWordOrCondition } from './hybridSearch.js';
import { normalizeRowsTimestamps } from '../utils/serialization.js';

/**
 * Provenance: 由来情報（mcp-tools.md §1.y準拠）
 */
export interface Provenance {
  at: string; // ISO8601 datetime (required)
  actor?: string;
  git?: {
    commit?: string;
    repo?: string;
    url?: string;
    files?: string[];
  };
  url?: string;
  note?: string;
  signed?: boolean;
}

export interface Claim {
  id: string;
  text: string;
  kind: string;
  scope: string;
  boundary_class: string;
  content_hash: string;
  // g()再ランキング用フィールド（ADR-0004準拠）
  utility: number;
  confidence: number;
  created_at: Date | string;
  updated_at: Date | string;
  // recency計算の基準時刻（positive feedbackでのみ更新）
  recency_anchor: Date | string;
  // 由来情報（mcp-tools.md §1.y準拠）
  provenance?: Provenance;
}

/**
 * upsertClaimの戻り値型
 * isNew: 新規挿入された場合はtrue、既存レコードを返した場合はfalse
 */
export interface UpsertResult {
  claim: Claim;
  isNew: boolean;
}

/**
 * Claimを登録（idempotent upsert）
 * 既存のcontent_hashがある場合は既存レコードを返す（isNew: false）
 * 新規の場合は挿入して返す（isNew: true）
 */
/** g()再ランキング用フィールドを含むClaim入力型 */
export type ClaimInput = Omit<
  Claim,
  'id' | 'utility' | 'confidence' | 'created_at' | 'updated_at' | 'recency_anchor'
> & {
  provenance?: Provenance;
};

/** 全カラムのSELECT句 */
const CLAIM_COLUMNS =
  'id, text, kind, scope, boundary_class, content_hash, utility, confidence, created_at, updated_at, recency_anchor, provenance';

/**
 * DBから取得したClaimのprovenanceフィールドをパース
 * DuckDBはJSON列を文字列として返すため、オブジェクトに変換する
 *
 * exactOptionalPropertyTypes対応: undefinedを代入せずプロパティを省略する
 */
function parseClaimProvenance(claim: Claim): Claim {
  if (claim.provenance && typeof claim.provenance === 'string') {
    try {
      return { ...claim, provenance: JSON.parse(claim.provenance) as Provenance };
    } catch {
      // パース失敗時はprovenanceプロパティを省略
      const { provenance: _, ...rest } = claim;
      return rest as Claim;
    }
  }
  return claim;
}

/**
 * 複数のClaimのprovenanceをパース
 */
function parseClaimsProvenance(claims: Claim[]): Claim[] {
  return claims.map(parseClaimProvenance);
}

export async function upsertClaim(c: ClaimInput): Promise<UpsertResult> {
  const conn = await getConnection();
  try {
    // 既存レコードをチェック
    const reader = await conn.runAndReadAll(
      `SELECT ${CLAIM_COLUMNS} FROM claims WHERE content_hash = $1`,
      [c.content_hash]
    );
    const rawExisting = reader.getRowObjects() as unknown as Claim[];
    const existing = parseClaimsProvenance(normalizeRowsTimestamps(rawExisting));
    if (existing.length > 0 && existing[0]) {
      return { claim: existing[0], isNew: false };
    }

    // 新規レコード挿入（utility/confidence/timestampsはDEFAULT値を使用）
    const id = `clm_${crypto.randomUUID().slice(0, 8)}`;
    const provenanceJson = c.provenance ? JSON.stringify(c.provenance) : null;
    await conn.run(
      'INSERT INTO claims (id, text, kind, scope, boundary_class, content_hash, provenance) VALUES ($1, $2, $3, $4, $5, $6, $7)',
      [id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash, provenanceJson]
    );
    // 挿入後のレコードを取得（DEFAULT値を含む）
    const insertedReader = await conn.runAndReadAll(
      `SELECT ${CLAIM_COLUMNS} FROM claims WHERE id = $1`,
      [id]
    );
    const rawInserted = insertedReader.getRowObjects() as unknown as Claim[];
    const inserted = parseClaimsProvenance(normalizeRowsTimestamps(rawInserted));
    return { claim: inserted[0]!, isNew: true };
  } catch (e: unknown) {
    // UNIQUE 制約違反などは既存レコードを返す（idempotent upsert）
    const reader = await conn.runAndReadAll(
      `SELECT ${CLAIM_COLUMNS} FROM claims WHERE content_hash = $1`,
      [c.content_hash]
    );
    const rawExisting = reader.getRowObjects() as unknown as Claim[];
    const existing = parseClaimsProvenance(normalizeRowsTimestamps(rawExisting));
    if (existing.length > 0 && existing[0]) {
      return { claim: existing[0], isNew: false };
    }
    throw e;
  }
}

/**
 * スコープ別Claim一覧取得（単語分割OR検索対応）
 *
 * 検索クエリは空白（半角・全角）で分割され、各単語のいずれかを含むClaimがマッチ。
 * 例: "状態管理 XState Valtio" → "状態管理" OR "XState" OR "Valtio"
 *
 * @param scopes スコープ配列
 * @param limit 結果上限
 * @param q 検索クエリ（オプション、空白区切りで複数単語指定可能）
 * @returns Claim配列
 */
export async function listClaimsByScope(
  scopes: string[],
  limit: number,
  q?: string
): Promise<Claim[]> {
  const conn = await getConnection();

  // DuckDBはプレースホルダーのIN句に配列をそのまま渡せないため、動的にSQL構築
  const placeholders = scopes.map((_, i) => `$${i + 1}`).join(',');

  // クエリを単語に分割
  const words = q ? splitQueryWords(q) : [];

  // 空クエリの場合はスコープ内の全Claimを返す
  if (words.length === 0) {
    const sql = `SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash,
              c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
              coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders})
       ORDER BY score DESC
       LIMIT $${scopes.length + 1}`;
    const reader = await conn.runAndReadAll(sql, [...scopes, limit]);
    const rawRows = reader.getRowObjects() as unknown as Claim[];
    return normalizeRowsTimestamps(rawRows);
  }

  // 単語OR条件を構築
  const { sql: wordCondition, params: wordParams } = buildWordOrCondition(words, scopes.length + 1);

  const sql = `SELECT c.id, c.text, c.kind, c.scope, c.boundary_class, c.content_hash,
              c.utility, c.confidence, c.created_at, c.updated_at, c.recency_anchor,
              coalesce(cr.score, 0) as score
       FROM claims c
       LEFT JOIN critic cr ON cr.claim_id = c.id
       WHERE c.scope IN (${placeholders}) AND ${wordCondition}
       ORDER BY score DESC
       LIMIT $${scopes.length + wordParams.length + 1}`;

  const reader = await conn.runAndReadAll(sql, [...scopes, ...wordParams, limit]);
  const rawRows = reader.getRowObjects() as unknown as Claim[];
  return normalizeRowsTimestamps(rawRows);
}

export async function findClaimById(id: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(`SELECT ${CLAIM_COLUMNS} FROM claims WHERE id = $1`, [
    id,
  ]);
  const rawRows = reader.getRowObjects() as unknown as Claim[];
  const rows = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  return rows[0];
}

/**
 * content_hashでClaimを検索
 */
export async function findClaimByContentHash(contentHash: string): Promise<Claim | undefined> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll(
    `SELECT ${CLAIM_COLUMNS} FROM claims WHERE content_hash = $1`,
    [contentHash]
  );
  const rawRows = reader.getRowObjects() as unknown as Claim[];
  const rows = parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
  return rows[0];
}

/**
 * フィルター条件によるClaim一覧取得（同期機能用）
 *
 * @param options フィルターオプション
 * @returns Claim配列
 */
export interface ClaimFilterOptions {
  scopes?: string[];
  boundaryClasses?: string[];
  since?: Date;
  limit?: number;
}

export async function listClaimsByFilter(options: ClaimFilterOptions): Promise<Claim[]> {
  const conn = await getConnection();
  const conditions: string[] = [];
  const params: (string | number)[] = [];
  let paramIndex = 1;

  // スコープフィルター
  if (options.scopes && options.scopes.length > 0) {
    const placeholders = options.scopes.map((_, i) => `$${paramIndex + i}`).join(',');
    conditions.push(`scope IN (${placeholders})`);
    params.push(...options.scopes);
    paramIndex += options.scopes.length;
  }

  // 境界クラスフィルター
  if (options.boundaryClasses && options.boundaryClasses.length > 0) {
    const placeholders = options.boundaryClasses.map((_, i) => `$${paramIndex + i}`).join(',');
    conditions.push(`boundary_class IN (${placeholders})`);
    params.push(...options.boundaryClasses);
    paramIndex += options.boundaryClasses.length;
  }

  // 日時フィルター（増分エクスポート用）
  if (options.since) {
    conditions.push(`created_at >= $${paramIndex}`);
    params.push(options.since.toISOString());
    paramIndex++;
  }

  // クエリ構築
  let sql = `SELECT ${CLAIM_COLUMNS} FROM claims`;
  if (conditions.length > 0) {
    sql += ` WHERE ${conditions.join(' AND ')}`;
  }
  sql += ` ORDER BY created_at DESC`;

  // リミット
  const limit = options.limit ?? 10000;
  sql += ` LIMIT $${paramIndex}`;
  params.push(limit);

  const reader = await conn.runAndReadAll(sql, params);
  const rawRows = reader.getRowObjects() as unknown as Claim[];
  return parseClaimsProvenance(normalizeRowsTimestamps(rawRows));
}

/**
 * Claimのboundary_classを更新（同期時のマージ用）
 *
 * @param id Claim ID
 * @param boundaryClass 新しいboundary_class
 */
export async function updateClaimBoundaryClass(id: string, boundaryClass: string): Promise<void> {
  const conn = await getConnection();
  await conn.run(
    'UPDATE claims SET boundary_class = $1, updated_at = CURRENT_TIMESTAMP WHERE id = $2',
    [boundaryClass, id]
  );
}

/**
 * DBに登録されているClaimの総数を取得
 * サーバー再起動時の状態復元に使用
 */
export async function countClaims(): Promise<number> {
  const conn = await getConnection();
  const reader = await conn.runAndReadAll('SELECT COUNT(*) as cnt FROM claims');
  const rows = reader.getRowObjects() as unknown as { cnt: number | bigint }[];
  return rows[0] ? Number(rows[0].cnt) : 0;
}

/**
 * Claimを登録し、埋め込みベクトルも生成・保存（ADR-0004対応）
 *
 * TLA+ 対応:
 * - 新規Claimの場合のみ埋め込みを生成
 * - 埋め込み生成失敗時もClaim登録は成功（ベストエフォート）
 *
 * @param c Claim（idなし）
 * @param embeddingService 埋め込みサービス
 * @returns UpsertResult（isNew: 新規かどうか）
 */
export async function upsertClaimWithEmbedding(
  c: ClaimInput,
  embeddingService: EmbeddingService
): Promise<UpsertResult> {
  // 1. 既存upsertClaim呼び出し
  const result = await upsertClaim(c);

  // 2. 新規の場合のみ埋め込み生成・保存
  if (result.isNew) {
    const embedResult = await embeddingService.embed({
      text: c.text,
      sensitivity: 'internal',
    })();

    // 埋め込み生成成功時のみ保存（失敗時はClaim登録だけ成功）
    if (E.isRight(embedResult)) {
      try {
        await saveClaimVector(
          result.claim.id,
          embedResult.right.embedding,
          embedResult.right.modelVersion
        );
      } catch {
        // ベクトル保存失敗は無視（ベストエフォート）
        // Claim登録は成功しているので、検索時はText-onlyで動作
      }
    }
  }

  return result;
}

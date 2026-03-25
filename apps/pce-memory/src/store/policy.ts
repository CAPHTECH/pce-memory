/**
 * ポリシー永続化ストア
 * ADR-0002対応: ポリシーをDBに永続化し、サーバー再起動時に復元可能にする
 * "Latest wins" 戦略: created_at DESC で最新ポリシーを取得
 */
import * as TE from 'fp-ts/TaskEither';
import { pipe } from 'fp-ts/function';
import { getConnection } from '../db/connection.js';
import type { DomainError } from '../domain/errors.js';
import { dbError } from '../domain/errors.js';
import { defaultPolicy } from '@pce/policy-schemas';
import type { BoundaryPolicy, PolicyDocument } from '@pce/policy-schemas';

// ========== 型定義 ==========

/** DB保存用ポリシーレコード */
export interface PolicyRecord {
  id: string;
  version: string;
  yaml_content: string;
  config_json: PolicyDocument;
  created_at: Date;
}

/** savePolicy結果 */
export interface SavePolicyResult {
  id: string;
  version: string;
}

// ========== 関数 ==========

/**
 * 旧形式（BoundaryPolicyのみ）を含む保存済みポリシーを正規化
 */
function isPolicyDocument(config: PolicyDocument | BoundaryPolicy): config is PolicyDocument {
  return 'boundary' in config;
}

function normalizePolicyDocument(
  version: string,
  config: PolicyDocument | BoundaryPolicy
): PolicyDocument {
  if (isPolicyDocument(config) && typeof config.boundary === 'object' && config.boundary !== null) {
    const retrieval = config.retrieval ?? defaultPolicy.retrieval;
    const maintenance = config.maintenance ?? defaultPolicy.maintenance;
    return {
      version: config.version ?? version,
      boundary: config.boundary,
      ...(retrieval ? { retrieval } : {}),
      ...(maintenance ? { maintenance } : {}),
    };
  }

  const retrieval = defaultPolicy.retrieval;
  const maintenance = defaultPolicy.maintenance;
  return {
    version,
    boundary: config as BoundaryPolicy,
    ...(retrieval ? { retrieval } : {}),
    ...(maintenance ? { maintenance } : {}),
  };
}

/**
 * ポリシーをDBに保存
 * @param version ポリシーバージョン
 * @param yamlContent 元のYAML文字列（空文字可）
 * @param policy パース済みPolicyDocumentまたは旧BoundaryPolicy
 */
export function savePolicy(
  version: string,
  yamlContent: string,
  policy: PolicyDocument | BoundaryPolicy
): TE.TaskEither<DomainError, SavePolicyResult> {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();
      const id = `pol_${crypto.randomUUID().slice(0, 8)}`;
      const normalizedPolicy = normalizePolicyDocument(version, policy);

      await conn.run(
        `INSERT INTO policies (id, version, yaml_content, config_json)
         VALUES ($1, $2, $3, $4)`,
        [id, version, yamlContent, JSON.stringify(normalizedPolicy)]
      );

      return { id, version };
    },
    (reason): DomainError => dbError(reason)
  );
}

/**
 * 最新のポリシーをDBから取得
 * "Latest wins" 戦略: created_at DESC で最新を取得
 * @returns ポリシーが存在しない場合はnone相当（Right(undefined)）
 */
export function loadLatestPolicy(): TE.TaskEither<DomainError, PolicyRecord | undefined> {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();

      const reader = await conn.runAndReadAll(
        `SELECT id, version, yaml_content, config_json, created_at
         FROM policies
         ORDER BY created_at DESC
         LIMIT 1`
      );

      const rows = reader.getRowObjects() as unknown as Array<{
        id: string;
        version: string;
        yaml_content: string;
        config_json: string;
        created_at: Date;
      }>;

      if (rows.length === 0) {
        return undefined;
      }

      const row = rows[0]!;
      const parsedConfig = JSON.parse(row.config_json) as PolicyDocument | BoundaryPolicy;
      return {
        id: row.id,
        version: row.version,
        yaml_content: row.yaml_content,
        config_json: normalizePolicyDocument(row.version, parsedConfig),
        created_at: row.created_at,
      };
    },
    (reason): DomainError => dbError(reason)
  );
}

/**
 * 指定バージョンのポリシーを取得
 * @param version 取得するバージョン
 */
export function loadPolicyByVersion(
  version: string
): TE.TaskEither<DomainError, PolicyRecord | undefined> {
  return TE.tryCatch(
    async () => {
      const conn = await getConnection();

      const reader = await conn.runAndReadAll(
        `SELECT id, version, yaml_content, config_json, created_at
         FROM policies
         WHERE version = $1
         ORDER BY created_at DESC
         LIMIT 1`,
        [version]
      );

      const rows = reader.getRowObjects() as unknown as Array<{
        id: string;
        version: string;
        yaml_content: string;
        config_json: string;
        created_at: Date;
      }>;

      if (rows.length === 0) {
        return undefined;
      }

      const row = rows[0]!;
      const parsedConfig = JSON.parse(row.config_json) as PolicyDocument | BoundaryPolicy;
      return {
        id: row.id,
        version: row.version,
        yaml_content: row.yaml_content,
        config_json: normalizePolicyDocument(row.version, parsedConfig),
        created_at: row.created_at,
      };
    },
    (reason): DomainError => dbError(reason)
  );
}

/**
 * ポリシーの存在チェック（初期化判定用）
 */
export function hasStoredPolicy(): TE.TaskEither<DomainError, boolean> {
  return pipe(
    loadLatestPolicy(),
    TE.map((record) => record !== undefined)
  );
}

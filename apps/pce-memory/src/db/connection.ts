import { DuckDBInstance, DuckDBConnection } from '@duckdb/node-api';
import { SCHEMA_SQL } from './schema.js';
import { computeContentHash } from '@pce/embeddings';

let instance: DuckDBInstance | null = null;
let cachedConnection: DuckDBConnection | null = null;

async function getTableColumns(
  conn: DuckDBConnection,
  tableName: string
): Promise<Map<string, { data_type: string; is_nullable: string }>> {
  const reader = await conn.runAndReadAll(
    'SELECT column_name, data_type, is_nullable FROM information_schema.columns WHERE table_name = $1',
    [tableName]
  );
  const rows = reader.getRowObjects() as unknown as Array<{
    column_name: string;
    data_type: string;
    is_nullable: string;
  }>;
  return new Map(
    rows.map((r) => [r.column_name, { data_type: r.data_type, is_nullable: r.is_nullable }])
  );
}

async function tableExists(conn: DuckDBConnection, tableName: string): Promise<boolean> {
  const reader = await conn.runAndReadAll(
    'SELECT COUNT(*)::INTEGER AS cnt FROM information_schema.tables WHERE table_name = $1',
    [tableName]
  );
  const rows = reader.getRowObjects() as unknown as Array<{ cnt: number | bigint }>;
  return Number(rows[0]?.cnt ?? 0) > 0;
}

function toLegacyObservationTags(input: unknown): string[] | undefined {
  if (input === undefined || input === null) return undefined;
  if (Array.isArray(input) && input.every((x) => typeof x === 'string')) return input as string[];
  if (typeof input !== 'string') return undefined;
  const parts = input
    .split(',')
    .map((t) => t.trim())
    .filter(Boolean);
  return parts.length > 0 ? parts : undefined;
}

function toDateFromLegacyCreatedAt(value: unknown): Date | undefined {
  // legacy: epoch seconds
  if (typeof value === 'number' && Number.isFinite(value)) return new Date(value * 1000);
  if (typeof value === 'bigint') return new Date(Number(value) * 1000);
  if (typeof value === 'string') {
    const asNumber = Number(value);
    if (Number.isFinite(asNumber) && value.trim() !== '') return new Date(asNumber * 1000);
    const d = new Date(value);
    if (!Number.isNaN(d.getTime())) return d;
  }
  return undefined;
}

/**
 * レガシーobservationsテーブルのマイグレーション
 *
 * Issue #30 Review: クラッシュ耐性を向上させるため「copy-and-swap」方式を採用
 * 1. 新スキーマで一時テーブルを作成
 * 2. 旧テーブルからデータをコピー
 * 3. 旧テーブルを削除（バックアップとしてリネームではなく削除）
 * 4. 一時テーブルをリネームして正式名にする
 *
 * これにより、クラッシュしても一時テーブルが残るだけで旧データは失われない
 */
async function migrateLegacyObservations(conn: DuckDBConnection): Promise<void> {
  if (!(await tableExists(conn, 'observations'))) return;

  const cols = await getTableColumns(conn, 'observations');
  const isLegacy =
    !cols.has('content_digest') || !cols.has('expires_at') || !cols.has('content_length');
  if (!isLegacy) return;

  const tempName = `observations_new_${crypto.randomUUID().slice(0, 8)}`;

  // Step 1: 新スキーマで一時テーブルを作成
  await conn.run(`
    CREATE TABLE ${tempName} (
      id TEXT PRIMARY KEY,
      source_type TEXT NOT NULL,
      source_id TEXT,
      content TEXT,
      content_digest TEXT NOT NULL,
      content_length INTEGER NOT NULL,
      actor TEXT,
      tags JSON,
      created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
      expires_at TIMESTAMP
    )
  `);
  await conn.run(`CREATE INDEX idx_${tempName}_expires_at ON ${tempName}(expires_at)`);

  // Step 2: 旧テーブルからデータをコピー
  const legacyReader = await conn.runAndReadAll('SELECT * FROM observations ORDER BY 1');
  const legacyRows = legacyReader.getRowObjects() as unknown as Array<Record<string, unknown>>;

  const defaultTtlDaysRaw = Number(process.env['PCE_OBS_TTL_DAYS'] ?? '30');
  const ttlDays =
    Number.isFinite(defaultTtlDaysRaw) && defaultTtlDaysRaw > 0 ? defaultTtlDaysRaw : 30;

  for (const row of legacyRows) {
    const id =
      row['id'] !== undefined ? String(row['id']) : `obs_${crypto.randomUUID().slice(0, 8)}`;
    const sourceType = typeof row['source_type'] === 'string' ? row['source_type'] : 'system';
    const sourceId = typeof row['source_id'] === 'string' ? row['source_id'] : null;
    const content = typeof row['content'] === 'string' ? row['content'] : '';
    const actor = typeof row['actor'] === 'string' ? row['actor'] : null;
    const tags = toLegacyObservationTags(row['tags']);
    const tagsJson = tags ? JSON.stringify(tags) : null;

    const createdAt = toDateFromLegacyCreatedAt(row['created_at']) ?? new Date();
    const expiresAt = new Date(createdAt.getTime() + ttlDays * 86_400_000).toISOString();

    const digest = `sha256:${computeContentHash(content)}`;
    const length = Buffer.byteLength(content, 'utf8');

    await conn.run(
      `INSERT INTO ${tempName} (id, source_type, source_id, content, content_digest, content_length, actor, tags, created_at, expires_at) VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9::TIMESTAMP, $10::TIMESTAMP) ON CONFLICT DO NOTHING`,
      [
        id,
        sourceType,
        sourceId,
        content,
        digest,
        length,
        actor,
        tagsJson,
        createdAt.toISOString(),
        expiresAt,
      ]
    );
  }

  // Step 3: 一時テーブルのインデックスを削除（DuckDBはテーブルリネーム時に依存関係エラーになるため）
  await conn.run(`DROP INDEX IF EXISTS idx_${tempName}_expires_at`);

  // Step 4: 旧テーブルを削除（copy-and-swap方式ではバックアップは不要）
  // 短期TTLのObservationデータなので、移行失敗時は再生成される想定
  await conn.run('DROP TABLE observations');

  // Step 5: 一時テーブルをリネーム
  await conn.run(`ALTER TABLE ${tempName} RENAME TO observations`);

  // Step 6: 新しいインデックスを作成
  await conn.run(
    'CREATE INDEX IF NOT EXISTS idx_observations_expires_at ON observations(expires_at)'
  );
}

/**
 * 孤立した一時テーブルをクリーンアップ
 *
 * マイグレーション中にクラッシュした場合、`claim_vectors_new_*` パターンの
 * テーブルが残存する可能性がある。起動時にこれらをクリーンアップする。
 */
async function cleanupOrphanedTempTables(conn: DuckDBConnection): Promise<void> {
  const reader = await conn.runAndReadAll(`
    SELECT table_name
    FROM information_schema.tables
    WHERE table_name LIKE 'claim_vectors_new_%'
  `);
  const rows = reader.getRowObjects() as unknown as Array<{ table_name: string }>;

  for (const row of rows) {
    console.error(`[DB] Cleaning up orphaned temp table: ${row.table_name}`);
    await conn.run(`DROP TABLE IF EXISTS "${row.table_name}"`);
  }
}

/**
 * claim_vectorsテーブルからFK制約を削除するマイグレーション
 *
 * DuckDBにはFK制約でUPDATE時にも誤ってエラーを発生させるバグがある。
 * 旧スキーマ（REFERENCES claims(id)付き）のDBを新スキーマ（FK制約なし）に移行する。
 *
 * copy-and-swap方式（トランザクション保護）:
 * 1. 孤立した一時テーブルをクリーンアップ
 * 2. トランザクション開始
 * 3. 新スキーマで一時テーブルを作成
 * 4. 旧テーブルからデータをコピー
 * 5. 旧テーブルを削除
 * 6. 一時テーブルをリネーム
 * 7. コミット（失敗時はロールバック）
 */
async function migrateClaimVectorsDropFK(conn: DuckDBConnection): Promise<void> {
  // まず孤立した一時テーブルをクリーンアップ
  await cleanupOrphanedTempTables(conn);

  if (!(await tableExists(conn, 'claim_vectors'))) return;

  // FK制約の有無を確認（DuckDBのduckdb_constraintsシステムテーブルを使用）
  const constraintReader = await conn.runAndReadAll(`
    SELECT constraint_type
    FROM duckdb_constraints()
    WHERE table_name = 'claim_vectors'
      AND constraint_type = 'FOREIGN KEY'
  `);
  const constraints = constraintReader.getRowObjects();

  // FK制約がない場合はマイグレーション不要
  if (constraints.length === 0) return;

  console.error('[DB] Migrating claim_vectors to remove FK constraint...');

  const tempName = `claim_vectors_new_${crypto.randomUUID().slice(0, 8)}`;

  // トランザクションで原子性を保証
  await conn.run('BEGIN TRANSACTION');
  try {
    // Step 1: 新スキーマで一時テーブルを作成（FK制約なし）
    await conn.run(`
      CREATE TABLE ${tempName} (
        claim_id TEXT PRIMARY KEY,
        embedding DOUBLE[] NOT NULL,
        model_version TEXT NOT NULL,
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      )
    `);

    // Step 2: 旧テーブルからデータをコピー
    await conn.run(`
      INSERT INTO ${tempName} (claim_id, embedding, model_version, created_at)
      SELECT claim_id, embedding, model_version, created_at FROM claim_vectors
    `);

    // Step 3: 旧テーブルのインデックスを削除（存在する場合）
    await conn.run('DROP INDEX IF EXISTS idx_claim_vectors_claim_id');

    // Step 4: 旧テーブルを削除
    await conn.run('DROP TABLE claim_vectors');

    // Step 5: 一時テーブルをリネーム
    await conn.run(`ALTER TABLE ${tempName} RENAME TO claim_vectors`);

    // Step 6: インデックスを再作成
    await conn.run(
      'CREATE INDEX IF NOT EXISTS idx_claim_vectors_claim_id ON claim_vectors(claim_id)'
    );

    await conn.run('COMMIT');
    console.error('[DB] claim_vectors FK migration completed');
  } catch (err) {
    await conn.run('ROLLBACK');
    console.error(`[DB] claim_vectors FK migration failed, rolled back: ${err}`);
    throw err;
  }
}

/**
 * DuckDB インスタンスを初期化（非同期）
 * 起動時に一度だけ呼び出す
 */
export async function initDb(): Promise<DuckDBInstance> {
  if (instance) return instance;
  const dbPath = process.env['PCE_DB'] ?? ':memory:';
  instance = await DuckDBInstance.create(dbPath);
  return instance;
}

/**
 * 初期化済みの DuckDB インスタンスを取得
 * initDb() が先に呼ばれている必要がある
 */
export function getDb(): DuckDBInstance {
  if (!instance) {
    throw new Error('Database not initialized. Call initDb() first.');
  }
  return instance;
}

/**
 * コネクションを取得（非同期）
 * 単一コネクションを再利用してリーク防止
 * 無効なコネクションは自動的に再作成
 */
export async function getConnection(): Promise<DuckDBConnection> {
  if (cachedConnection) {
    try {
      // コネクションが有効かを簡単なクエリで確認
      await cachedConnection.runAndReadAll('SELECT 1');
      return cachedConnection;
    } catch {
      // コネクションが無効な場合は再作成
      try {
        cachedConnection.closeSync();
      } catch {
        // クローズエラーは無視
      }
      cachedConnection = null;
    }
  }
  cachedConnection = await getDb().connect();
  return cachedConnection;
}

/**
 * スキーマを初期化（非同期）
 */
export async function initSchema() {
  const conn = await getConnection();

  // 過去バージョン互換のマイグレーション
  // - SCHEMA_SQL内のCREATE INDEXが旧テーブルに対して失敗しないよう、先に実施する
  await migrateLegacyObservations(conn); // Issue #30: observationsスキーマ変更
  await migrateClaimVectorsDropFK(conn); // PR #32: DuckDB FK制約バグ対策

  const statements = SCHEMA_SQL.split(';')
    .map((s) => s.trim())
    .filter(Boolean);
  for (const stmt of statements) {
    await conn.run(stmt);
  }
}

/**
 * テスト用: DB をリセット（非同期版を推奨）
 * 互換性のため同期版も維持
 */
export function resetDb(): void {
  // 注意: この関数はコネクションを適切にクローズしない
  // 可能であれば resetDbAsync() を使用すること
  cachedConnection = null;
  instance = null;
}

/**
 * テスト用: DB をリセット（非同期）
 * コネクションを適切にクローズしてからリセット
 */
export async function resetDbAsync(): Promise<void> {
  if (cachedConnection) {
    try {
      // DuckDB Node APIはcloseSync()を使用
      cachedConnection.closeSync();
    } catch {
      // クローズエラーは無視（既にクローズされている可能性）
    }
  }
  cachedConnection = null;
  instance = null;
}

/**
 * DB接続を明示的にクローズ（デーモンシャットダウン用）
 * DuckDBロックを解放し、他のプロセスがDBにアクセスできるようにする
 *
 * @remarks
 * - CHECKPOINT実行でWALをDBファイルにフラッシュ（データ永続化保証）
 * - cachedConnection.closeSync() でDuckDBファイルロックを解放
 * - DuckDBInstanceはcloseメソッドを持たないため、参照解放でGCに委ねる
 * - 複数回呼び出しても安全（冪等）
 *
 * TODO: @duckdb/node-api の将来バージョンで DuckDBInstance.close() が追加された場合、
 *       明示的なクローズ処理に切り替えること。
 *       関連: https://github.com/duckdb/duckdb-node-neo/issues
 */
export async function closeDb(): Promise<void> {
  if (cachedConnection) {
    try {
      // WALをDBファイルにフラッシュしてからクローズ
      // これにより、シャットダウン後の再起動時にWALリプレイ問題を回避
      await cachedConnection.run('CHECKPOINT');
      console.error('[DB] Checkpoint completed');
    } catch (err) {
      // :memory:DBの場合はCHECKPOINT不要なのでスキップ扱い
      // ファイルベースDBの場合はデータ永続化に影響する可能性があるため警告
      const dbPath = process.env['PCE_DB'] ?? ':memory:';
      if (dbPath === ':memory:') {
        // in-memory DBではCHECKPOINTは不要（WALが存在しない）
      } else {
        console.error(`[DB] Checkpoint failed (non-fatal, data may not be fully persisted): ${err}`);
      }
    }

    try {
      cachedConnection.closeSync();
    } catch (err) {
      console.error(`[DB] Failed to close connection: ${err}`);
    }
    cachedConnection = null;
  }

  // DuckDBInstanceはcloseメソッドを持たないため、参照を解放
  // GCによってリソースが解放される
  instance = null;
}

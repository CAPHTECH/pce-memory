/**
 * PCE Memory MCP Server (stdio)
 * 本番用の最小実装: DuckDB ストア + ポリシー適用 + 境界チェック + upsert/activate/feedback
 *
 * ADR-0002に基づく状態機械APIパターンを採用:
 * - 実行時状態検証により不正な操作順序を防止
 * - Uninitialized → PolicyApplied → HasClaims → Ready の遷移を強制
 * - PCEMemoryクラスを直接使用（StateManager廃止）
 */
import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  ListToolsRequestSchema,
  CallToolRequestSchema,
  ListPromptsRequestSchema,
  GetPromptRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import {
  initLocalProvider,
  localProvider,
  createInMemoryCache,
  createLocalOnlyService,
} from '@pce/embeddings';
import { initDb, initSchema } from './db/connection.js';
import { setEmbeddingService } from './store/hybridSearch.js';
import { setAuditLogPath } from './store/logs.js';
import { initRateState } from './store/rate.js';
import { loadEnv } from './config/env.js';
import { sanitizeErrorMessage } from './audit/filter.js';
import * as E from 'fp-ts/Either';

// memoryState モジュールから状態管理関数をインポート
import { initMemoryState } from './state/memoryState.js';

// layerScopeState モジュールからLayer/Scope管理関数をインポート
import { registerSystemLayer, getLayerScopeSummary } from './state/layerScopeState.js';

// Core handlers from handlers.ts（重複を排除して一元化）
import {
  dispatchTool,
  TOOL_DEFINITIONS,
  handleListPrompts,
  handleGetPrompt,
} from './core/handlers.js';

// サーバー情報
const SERVER_NAME = 'pce-memory';
const SERVER_VERSION = '0.1.0';

/**
 * MCP ツールハンドラの登録（CallToolRequestSchema を使用）
 * dispatchToolを使用して一元化されたハンドラにディスパッチ
 */
async function registerTools(server: Server) {
  server.setRequestHandler(CallToolRequestSchema, async (request) => {
    const { name, arguments: args } = request.params;
    const toolArgs = (args ?? {}) as Record<string, unknown>;
    return dispatchTool(name, toolArgs);
  });
}

export async function main() {
  // 環境変数読み込み
  const env = loadEnv();

  // 監査ログファイルパスを設定
  setAuditLogPath(env.AUDIT_LOG_PATH);

  // DB初期化（非同期）
  await initDb();
  await initSchema();
  await initRateState();

  // EmbeddingService初期化（ADR-0004 Hybrid Search用）
  try {
    await initLocalProvider();
    const embeddingCache = createInMemoryCache({ initialModelVersion: localProvider.modelVersion });
    const embeddingService = createLocalOnlyService(localProvider, embeddingCache);
    setEmbeddingService(embeddingService);
    console.error(
      `[${SERVER_NAME}] EmbeddingService initialized (model: ${localProvider.modelVersion})`
    );
  } catch (e: unknown) {
    // 埋め込み初期化失敗時はText-only検索で動作（ベストエフォート）
    console.error(
      `[${SERVER_NAME}] EmbeddingService initialization failed (fallback to text-only search):`,
      e
    );
  }

  // システムLayer登録（ADR-0001 V2 Effect設計）
  // TLA+ RegisterLayerに対応: 依存グラフを構築
  const dbLayerResult = registerSystemLayer('db', new Set(['db_access'] as const), new Set());
  if (E.isLeft(dbLayerResult)) {
    console.error(`[${SERVER_NAME}] Failed to register db layer: ${dbLayerResult.left.message}`);
  }

  const policyLayerResult = registerSystemLayer(
    'policy',
    new Set(['policy_check'] as const),
    new Set(['db']) // policyはdbに依存
  );
  if (E.isLeft(policyLayerResult)) {
    console.error(
      `[${SERVER_NAME}] Failed to register policy layer: ${policyLayerResult.left.message}`
    );
  }

  const schemaLayerResult = registerSystemLayer(
    'schema',
    new Set(['schema_validate'] as const),
    new Set(['db']) // schemaはdbに依存
  );
  if (E.isLeft(schemaLayerResult)) {
    console.error(
      `[${SERVER_NAME}] Failed to register schema layer: ${schemaLayerResult.left.message}`
    );
  }

  console.error(
    `[${SERVER_NAME}] System layers registered: ${getLayerScopeSummary().layers.join(', ')}`
  );

  // 状態復元: memoryStateモジュールの初期化
  // DBからポリシーとclaim数を読み込み、適切な状態に復元
  const initResult = await initMemoryState()();
  if (E.isLeft(initResult)) {
    console.error(`[${SERVER_NAME}] Failed to initialize state: ${initResult.left.message}`);
    // 初期化失敗時はUninitializedのまま起動（policy.applyで初期化可能）
  } else {
    console.error(
      `[${SERVER_NAME}] Restored state: ${initResult.right.state} (policy: ${initResult.right.policyVersion})`
    );
  }

  // サーバー作成（名前とバージョンを指定）
  // MCP capabilities: tools + prompts (Issue #16)
  const server = new Server(
    { name: SERVER_NAME, version: SERVER_VERSION },
    {
      capabilities: {
        tools: {},
        prompts: {},
      },
    }
  );

  // ListToolsハンドラ登録
  server.setRequestHandler(ListToolsRequestSchema, async () => {
    return { tools: TOOL_DEFINITIONS };
  });

  // ListPromptsハンドラ登録 (Issue #16)
  server.setRequestHandler(ListPromptsRequestSchema, async (request) => {
    const result = await handleListPrompts(request.params ?? {});
    return result;
  });

  // GetPromptハンドラ登録 (Issue #16)
  server.setRequestHandler(GetPromptRequestSchema, async (request) => {
    const result = await handleGetPrompt(request.params);
    return result;
  });

  // ツールハンドラ登録
  await registerTools(server);

  // トランスポート接続
  const transport = new StdioServerTransport();
  await server.connect(transport);

  // Graceful shutdown ハンドラ
  const shutdown = async (signal: string) => {
    console.error(`[${SERVER_NAME}] Received ${signal}, shutting down...`);
    try {
      await server.close();
    } catch (e) {
      console.error(`[${SERVER_NAME}] Error during shutdown:`, sanitizeErrorMessage(e));
    }
    process.exit(0);
  };

  process.on('SIGINT', () => shutdown('SIGINT'));
  process.on('SIGTERM', () => shutdown('SIGTERM'));
}

main().catch((err) => {
  console.error(`[${SERVER_NAME}] Fatal error:`, sanitizeErrorMessage(err));
  process.exit(1);
});

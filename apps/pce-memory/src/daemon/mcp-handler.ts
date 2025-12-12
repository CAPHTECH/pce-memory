import type { JsonRpcRequest, JsonRpcResponse } from './socket.js';
import {
  dispatchTool,
  TOOL_DEFINITIONS,
  handleListPrompts,
  handleGetPrompt,
} from '../core/handlers.js';

export interface McpJsonRpcRequestHandlerOptions {
  serverName: string;
  serverVersion: string;
  protocolVersion: string;
  promptsListChanged?: boolean;
}

/**
 * JSON-RPCリクエストハンドラ（daemon向け）
 *
 * - stdioサーバーは @modelcontextprotocol/sdk に委譲
 * - daemonは自前のsocket transportのため、MCPの主要メソッドをここで実装する
 */
export function createMcpJsonRpcRequestHandler(options: McpJsonRpcRequestHandlerOptions) {
  const promptsListChanged = options.promptsListChanged ?? false;

  return async function handleJsonRpcRequest(
    request: JsonRpcRequest
  ): Promise<JsonRpcResponse | null> {
    const { method, params, id } = request;

    // pingリクエスト（ヘルスチェック用）
    if (method === 'ping') {
      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result: {
          status: 'ok',
          serverInfo: {
            name: options.serverName,
            version: options.serverVersion,
          },
        },
      };
    }

    // MCP initialize（MCPプロトコル必須）
    if (method === 'initialize') {
      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result: {
          protocolVersion: options.protocolVersion,
          capabilities: {
            tools: {},
            prompts: { listChanged: promptsListChanged },
          },
          serverInfo: {
            name: options.serverName,
            version: options.serverVersion,
          },
        },
      };
    }

    // MCP notifications/initialized（初期化完了通知、レスポンス不要）
    if (method === 'notifications/initialized') {
      return null;
    }

    // MCP tools/list（ツール一覧）
    if (method === 'tools/list') {
      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result: { tools: TOOL_DEFINITIONS },
      };
    }

    // MCP prompts/list（プロンプト一覧）
    if (method === 'prompts/list') {
      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result: await handleListPrompts(params ?? {}),
      };
    }

    // MCP prompts/get（プロンプト取得）
    if (method === 'prompts/get') {
      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result: await handleGetPrompt(params ?? {}),
      };
    }

    // MCP tools/call（ツール呼び出し）
    if (method === 'tools/call') {
      const toolName = (params as Record<string, unknown>)?.['name'] as string;
      const toolArgs = ((params as Record<string, unknown>)?.['arguments'] ?? {}) as Record<
        string,
        unknown
      >;

      const result = await dispatchTool(toolName, toolArgs);

      return {
        jsonrpc: '2.0',
        id: id ?? null,
        result,
      };
    }

    // 未知のメソッド
    return {
      jsonrpc: '2.0',
      id: id ?? null,
      error: {
        code: -32601,
        message: `Method not found: ${method}`,
      },
    };
  };
}

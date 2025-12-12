import { describe, it, expect } from 'vitest';

import { createMcpJsonRpcRequestHandler } from '../src/daemon/mcp-handler.js';

describe('daemon MCP JSON-RPC handler', () => {
  const handler = createMcpJsonRpcRequestHandler({
    serverName: 'pce-memory-daemon',
    serverVersion: '0.0.0-test',
    protocolVersion: '2024-11-05',
  });

  it('initialize advertises prompts capability', async () => {
    const res = await handler({ jsonrpc: '2.0', id: 1, method: 'initialize', params: {} });

    expect(res).toMatchObject({
      jsonrpc: '2.0',
      id: 1,
      result: {
        protocolVersion: '2024-11-05',
        capabilities: {
          tools: {},
          prompts: { listChanged: false },
        },
      },
    });
  });

  it('supports prompts/list', async () => {
    const res = await handler({ jsonrpc: '2.0', id: 2, method: 'prompts/list', params: {} });

    expect(res).toMatchObject({
      jsonrpc: '2.0',
      id: 2,
    });

    const prompts = (res as any)?.result?.prompts as Array<{ name: string }> | undefined;
    expect(prompts?.length).toBeGreaterThan(0);
    expect(prompts?.map((p) => p.name)).toContain('recall_context');
  });

  it('supports prompts/get', async () => {
    const res = await handler({
      jsonrpc: '2.0',
      id: 3,
      method: 'prompts/get',
      params: { name: 'recall_context', arguments: { query: '認証', scope: 'project' } },
    });

    expect(res).toMatchObject({
      jsonrpc: '2.0',
      id: 3,
    });

    const messages = (res as any)?.result?.messages as Array<unknown> | undefined;
    expect(messages?.length).toBeGreaterThan(0);
  });
});

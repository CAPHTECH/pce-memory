import { afterEach, describe, expect, it } from 'vitest';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { once } from 'node:events';
import {
  extractEntitiesWithLLM,
  LLM_EXTRACTION_TIMEOUT_MS,
} from '../src/store/llmEntityExtractor.js';

type RequestHandler = (
  req: IncomingMessage,
  res: ServerResponse<IncomingMessage>
) => void | Promise<void>;

interface TestServer {
  endpoint: string;
  close: () => Promise<void>;
}

const activeServers = new Set<TestServer>();

async function startServer(handler: RequestHandler): Promise<TestServer> {
  const server = createServer(async (req, res) => {
    try {
      await handler(req, res);
    } catch (error) {
      res.statusCode = 500;
      res.setHeader('content-type', 'application/json');
      res.end(
        JSON.stringify({
          error: error instanceof Error ? error.message : String(error),
        })
      );
    }
  });

  server.listen(0, '127.0.0.1');
  await once(server, 'listening');
  const address = server.address();
  if (!address || typeof address === 'string') {
    throw new Error('Failed to resolve test server address');
  }

  const testServer: TestServer = {
    endpoint: `http://127.0.0.1:${address.port}`,
    close: async () => {
      server.close();
      await once(server, 'close');
    },
  };
  activeServers.add(testServer);
  return testServer;
}

afterEach(async () => {
  const closers = [...activeServers];
  activeServers.clear();
  for (const server of closers) {
    await server.close();
  }
});

describe('extractEntitiesWithLLM', () => {
  it('calls the Ollama chat completions endpoint and deduplicates entities and relations', async () => {
    let requestPath = '';
    let requestBody = '';
    const server = await startServer(async (req, res) => {
      requestPath = req.url ?? '';
      const chunks: Buffer[] = [];
      for await (const chunk of req) {
        chunks.push(Buffer.isBuffer(chunk) ? chunk : Buffer.from(chunk));
      }
      requestBody = Buffer.concat(chunks).toString('utf8');

      res.statusCode = 200;
      res.setHeader('content-type', 'application/json');
      res.end(
        JSON.stringify({
          choices: [
            {
              message: {
                content: `\`\`\`json
{"entities":[{"name":"JWT","type":"Technology","canonical_key":"jwt"},{"name":"Authentication","type":"Concept","canonical_key":"authentication"},{"name":"JWT","type":"Artifact","canonical_key":"jwt"}],"relations":[{"src":"authentication","dst":"jwt","type":"uses"},{"source":"Authentication","target":"JWT","relation":"uses"}]}
\`\`\``,
              },
            },
          ],
        })
      );
    });

    const result = await extractEntitiesWithLLM('Authentication uses JWT access tokens.', {
      ollamaEndpoint: server.endpoint,
      model: 'test-model',
    });

    expect(requestPath).toBe('/v1/chat/completions');
    expect(JSON.parse(requestBody)).toMatchObject({
      model: 'test-model',
      stream: false,
      temperature: 0,
    });
    expect(result.entities).toEqual([
      {
        name: 'JWT',
        type: 'Artifact',
        canonical_key: 'jwt',
      },
      {
        name: 'Authentication',
        type: 'Concept',
        canonical_key: 'authentication',
      },
    ]);
    expect(result.relations).toEqual([
      {
        src: 'authentication',
        dst: 'jwt',
        type: 'USES',
      },
    ]);
  });

  it('drops invalid entities and relations that do not match the expected schema', async () => {
    const server = await startServer((_req, res) => {
      res.statusCode = 200;
      res.setHeader('content-type', 'application/json');
      res.end(
        JSON.stringify({
          choices: [
            {
              message: {
                content: JSON.stringify({
                  entities: [
                    { name: 'JWT', type: 'Technology' },
                    { type: 'Concept', canonical_key: 'missing-name' },
                    { name: '', type: 'Concept' },
                    { name: 'Authentication', type: 'Concept', canonical_key: 'authentication' },
                  ],
                  relations: [
                    { src: 'authentication', dst: 'jwt', type: 'depends on' },
                    { src: 'authentication', dst: 'missing', type: 'uses' },
                    { src: 'authentication', dst: 'authentication', type: 'uses' },
                  ],
                }),
              },
            },
          ],
        })
      );
    });

    const result = await extractEntitiesWithLLM('Authentication depends on JWT.', {
      ollamaEndpoint: server.endpoint,
    });

    expect(result.entities).toEqual([
      {
        name: 'JWT',
        type: 'Artifact',
        canonical_key: 'jwt',
      },
      {
        name: 'Authentication',
        type: 'Concept',
        canonical_key: 'authentication',
      },
    ]);
    expect(result.relations).toEqual([
      {
        src: 'authentication',
        dst: 'jwt',
        type: 'DEPENDS_ON',
      },
    ]);
  });

  it('returns empty results when Ollama is unavailable', async () => {
    const result = await extractEntitiesWithLLM('JWT authentication', {
      ollamaEndpoint: 'http://127.0.0.1:9',
    });

    expect(result).toEqual({ entities: [], relations: [] });
  });

  it(
    'aborts long-running requests after the extraction timeout',
    async () => {
      const server = await startServer(async (_req, res) => {
        await new Promise((resolve) => setTimeout(resolve, LLM_EXTRACTION_TIMEOUT_MS + 250));
        res.statusCode = 200;
        res.setHeader('content-type', 'application/json');
        res.end(
          JSON.stringify({
            choices: [
              {
                message: {
                  content: JSON.stringify({
                    entities: [{ name: 'Late', type: 'Concept', canonical_key: 'late' }],
                    relations: [],
                  }),
                },
              },
            ],
          })
        );
      });

      const startedAt = Date.now();
      const result = await extractEntitiesWithLLM('This response should time out.', {
        ollamaEndpoint: server.endpoint,
      });
      const durationMs = Date.now() - startedAt;

      expect(result).toEqual({ entities: [], relations: [] });
      expect(durationMs).toBeLessThan(LLM_EXTRACTION_TIMEOUT_MS + 1_500);
    },
    8_000
  );
});

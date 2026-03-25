import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { once } from 'node:events';
import { stringify } from 'yaml';
import { defaultPolicy } from '@pce/policy-schemas';
import { dispatchTool } from '../src/core/handlers.js';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { getEntitiesForClaim } from '../src/store/entities.js';
import { getRelationsByEvidence } from '../src/store/relations.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import { resetLayerScopeState } from '../src/state/layerScopeState.js';
import { initRateState, resetRates } from '../src/store/rate.js';

interface TestServer {
  endpoint: string;
  close: () => Promise<void>;
}

const activeServers = new Set<TestServer>();

async function startServer(
  handler: (req: IncomingMessage, res: ServerResponse<IncomingMessage>) => void | Promise<void>
): Promise<TestServer> {
  const server = createServer(async (req, res) => {
    await handler(req, res);
  });
  server.listen(0, '127.0.0.1');
  await once(server, 'listening');
  const address = server.address();
  if (!address || typeof address === 'string') {
    throw new Error('Failed to resolve mock Ollama server address');
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

function expectSuccess(result: Awaited<ReturnType<typeof dispatchTool>>) {
  expect(result.isError).toBeUndefined();
  expect(result.structuredContent).toBeDefined();
  return result.structuredContent!;
}

async function applyPolicyWithLlm(endpoint: string) {
  const result = await dispatchTool('pce_memory_policy_apply', {
    yaml: stringify({
      ...defaultPolicy,
      extraction: {
        llm_enabled: true,
        ollama_endpoint: endpoint,
        model: 'test-model',
      },
    }),
  });
  expect(result.isError).toBeUndefined();
}

beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

afterEach(async () => {
  const closers = [...activeServers];
  activeServers.clear();
  for (const server of closers) {
    await server.close();
  }
});

describe('LLM-backed promotion graph materialization', () => {
  it('stores proposed entities during distill and links them on promote', async () => {
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
                    { name: 'Authentication', type: 'Concept', canonical_key: 'authentication' },
                    { name: 'JWT', type: 'Technology', canonical_key: 'jwt' },
                    { name: 'Refresh Token', type: 'Config', canonical_key: 'refresh-token' },
                  ],
                  relations: [
                    { src: 'authentication', dst: 'jwt', type: 'uses' },
                    { src: 'authentication', dst: 'refresh-token', type: 'uses' },
                  ],
                }),
              },
            },
          ],
        })
      );
    });
    await applyPolicyWithLlm(server.endpoint);

    const observation = expectSuccess(
      await dispatchTool('pce_memory_observe', {
        source_type: 'chat',
        content:
          'Authentication architecture uses JWT access tokens and refresh token rotation for session security.',
        boundary_class: 'internal',
        extract: { mode: 'noop' },
      })
    );

    const distill = expectSuccess(
      await dispatchTool('pce_memory_distill', {
        source_observation_ids: [observation.observation_id],
        note: 'auth architecture candidate',
      })
    );

    const conn = await getConnection();
    const queueReader = await conn.runAndReadAll(
      'SELECT proposed_entities, proposed_relations FROM promotion_queue WHERE id = $1',
      [distill.candidate_id]
    );
    const queueRows = queueReader.getRowObjects() as Array<{
      proposed_entities: string;
      proposed_relations: string;
    }>;
    const proposedEntities = JSON.parse(queueRows[0]?.proposed_entities ?? '[]') as Array<{
      canonical_key: string;
    }>;
    const proposedRelations = JSON.parse(queueRows[0]?.proposed_relations ?? '[]') as Array<{
      type: string;
    }>;

    expect(proposedEntities.map((entity) => entity.canonical_key)).toEqual(
      expect.arrayContaining(['authentication', 'jwt', 'refresh-token'])
    );
    expect(proposedRelations.map((relation) => relation.type)).toEqual(
      expect.arrayContaining(['USES'])
    );

    const promote = expectSuccess(
      await dispatchTool('pce_memory_promote', {
        candidate_id: distill.candidate_id,
        provenance: { at: '2025-01-01T00:00:00.000Z', actor: 'claude' },
      })
    );

    const entities = await getEntitiesForClaim(promote.claim_id as string);
    expect(entities.map((entity) => entity.canonical_key)).toEqual(
      expect.arrayContaining(['authentication', 'jwt', 'refresh-token'])
    );

    const relations = await getRelationsByEvidence(promote.claim_id as string);
    expect(relations).toHaveLength(2);
    expect(relations.map((relation) => relation.type)).toEqual(expect.arrayContaining(['USES']));
  });
});

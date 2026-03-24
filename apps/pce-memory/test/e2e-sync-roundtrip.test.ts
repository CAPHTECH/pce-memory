import { afterEach, beforeEach, describe, expect, it } from 'vitest';
import * as fs from 'node:fs/promises';
import * as os from 'node:os';
import * as path from 'node:path';
import { computeContentHash } from '@pce/embeddings';
import { dispatchTool } from '../src/core/handlers.js';
import { getConnection, initDb, initSchema, resetDbAsync } from '../src/db/connection.js';
import { resetLayerScopeState } from '../src/state/layerScopeState.js';
import { resetMemoryState } from '../src/state/memoryState.js';
import { findClaimByContentHash, findClaimById, countClaims } from '../src/store/claims.js';
import { findEntityById } from '../src/store/entities.js';
import { initRateState, resetRates } from '../src/store/rate.js';
import { findRelationById } from '../src/store/relations.js';
import { listJsonFiles } from '../src/sync/fileSystem.js';
import type { ClaimKind, MemoryType } from '../src/domain/types.js';
import type { ClaimExport } from '../src/sync/schemas.js';

type ToolResult = Awaited<ReturnType<typeof dispatchTool>>;

type UpsertResponse = {
  id: string;
  is_new: boolean;
  content_hash: string;
};

type ObserveResponse = {
  observation_id: string;
  claim_ids: string[];
};

type DistillResponse = {
  candidate_id: string;
  distilled_text: string;
};

type PromoteResponse = {
  claim_id: string;
  rollback_token: string;
};

type SyncPushResponse = {
  exported: {
    claims: number;
    entities: number;
    relations: number;
  };
  target_dir: string;
  manifest_updated: boolean;
};

type SyncPullResponse = {
  imported: {
    claims: {
      new: number;
      skipped_duplicate: number;
      upgraded_boundary: number;
      skipped_by_since: number;
    };
    entities: {
      new: number;
      skipped_duplicate: number;
    };
    relations: {
      new: number;
      skipped_duplicate: number;
    };
  };
  manifest_updated: boolean;
};

type DurableClaimInput = {
  text: string;
  kind?: ClaimKind;
  scope?: 'project' | 'principle';
  boundary_class?: 'public' | 'internal' | 'pii';
  memory_type?: Exclude<MemoryType, 'evidence'>;
  provenanceAt?: string;
  entities?: Array<{
    id: string;
    type: 'Actor' | 'Artifact' | 'Event' | 'Concept';
    name: string;
  }>;
  relations?: Array<{
    id: string;
    src_id: string;
    dst_id: string;
    type: string;
  }>;
};

const ORIGINAL_CWD = process.cwd();
const SYNC_DIR_NAME = '.pce-shared';
const BASE_AT = Date.parse('2026-03-24T00:00:00.000Z');

let tempDir: string;

function atMinutes(offsetMinutes: number): string {
  return new Date(BASE_AT + offsetMinutes * 60_000).toISOString();
}

function contentHashFor(text: string): string {
  return `sha256:${computeContentHash(text)}`;
}

function claimExportPath(scope: 'project' | 'principle', text: string): string {
  return path.join(
    tempDir,
    SYNC_DIR_NAME,
    'claims',
    scope,
    `${computeContentHash(text)}.json`
  );
}

function unwrapStructured<T extends Record<string, unknown>>(result: ToolResult): T {
  if (result.isError) {
    throw new Error(result.content[0]?.text ?? 'tool call failed');
  }
  if (!result.structuredContent) {
    throw new Error('missing structuredContent');
  }
  return result.structuredContent as T;
}

async function applyPolicy(): Promise<void> {
  unwrapStructured(await dispatchTool('pce_memory_policy_apply', {}));
}

async function resetRuntime(): Promise<void> {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  process.env.PCE_RATE_CAP = '100';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
  await applyPolicy();
}

async function syncPush(args: Record<string, unknown> = {}): Promise<SyncPushResponse> {
  return unwrapStructured<SyncPushResponse>(await dispatchTool('pce_memory_sync_push', args));
}

async function syncPull(args: Record<string, unknown> = {}): Promise<SyncPullResponse> {
  return unwrapStructured<SyncPullResponse>(await dispatchTool('pce_memory_sync_pull', args));
}

async function upsertDurableClaim(input: DurableClaimInput): Promise<UpsertResponse> {
  const text = input.text;
  return unwrapStructured<UpsertResponse>(
    await dispatchTool('pce_memory_upsert', {
      text,
      kind: input.kind ?? 'fact',
      scope: input.scope ?? 'project',
      boundary_class: input.boundary_class ?? 'internal',
      ...(input.memory_type ? { memory_type: input.memory_type } : {}),
      content_hash: contentHashFor(text),
      provenance: {
        at: input.provenanceAt ?? atMinutes(0),
        actor: 'vitest',
      },
      ...(input.entities ? { entities: input.entities } : {}),
      ...(input.relations ? { relations: input.relations } : {}),
    })
  );
}

async function observeSessionContent(
  content: string,
  boundary_class: 'public' | 'internal' | 'pii' | 'secret' = 'internal'
): Promise<ObserveResponse> {
  return unwrapStructured<ObserveResponse>(
    await dispatchTool('pce_memory_observe', {
      source_type: 'chat',
      content,
      boundary_class,
      extract: { mode: 'noop' },
    })
  );
}

async function promoteObservedContent(
  content: string,
  provenanceAt: string
): Promise<{ distill: DistillResponse; promote: PromoteResponse }> {
  const observation = await observeSessionContent(content);
  const distill = unwrapStructured<DistillResponse>(
    await dispatchTool('pce_memory_distill', {
      source_observation_ids: [observation.observation_id],
      note: 'round-trip candidate',
    })
  );
  const promote = unwrapStructured<PromoteResponse>(
    await dispatchTool('pce_memory_promote', {
      candidate_id: distill.candidate_id,
      provenance: {
        at: provenanceAt,
        actor: 'vitest',
      },
    })
  );
  return { distill, promote };
}

async function rollbackClaim(claimId: string, provenanceAt: string): Promise<void> {
  unwrapStructured(
    await dispatchTool('pce_memory_rollback', {
      claim_id: claimId,
      reason: 'round-trip rollback',
      provenance: {
        at: provenanceAt,
        actor: 'vitest',
      },
    })
  );
}

async function readClaimExport(scope: 'project' | 'principle', text: string): Promise<ClaimExport> {
  const filePath = claimExportPath(scope, text);
  return JSON.parse(await fs.readFile(filePath, 'utf-8')) as ClaimExport;
}

async function readAllExportedClaims(): Promise<ClaimExport[]> {
  const claimFiles = await listJsonFiles(path.join(tempDir, SYNC_DIR_NAME, 'claims'), true);
  return Promise.all(
    claimFiles.map(async (filePath) => JSON.parse(await fs.readFile(filePath, 'utf-8')) as ClaimExport)
  );
}

async function pathExists(targetPath: string): Promise<boolean> {
  try {
    await fs.access(targetPath);
    return true;
  } catch {
    return false;
  }
}

beforeEach(async () => {
  tempDir = await fs.mkdtemp(path.join(os.tmpdir(), 'pce-sync-roundtrip-test-'));
  process.chdir(tempDir);
  await resetRuntime();
});

afterEach(async () => {
  process.chdir(ORIGINAL_CWD);
  await fs.rm(tempDir, { recursive: true, force: true });
});

describe('sync round-trip E2E', () => {
  it('BASIC ROUND-TRIP: preserves memory_type across push, file export, and pull', async () => {
    const text = 'round-trip durable knowledge';

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(1),
    });

    const push = await syncPush();
    expect(push.exported.claims).toBe(1);

    const exported = await readClaimExport('project', text);
    expect(exported.memory_type).toBe('knowledge');
    expect(exported.content_hash).toBe(contentHashFor(text));

    await resetRuntime();

    const pull = await syncPull();
    expect(pull.imported.claims.new).toBe(1);

    const restored = await findClaimByContentHash(contentHashFor(text));
    expect(restored?.text).toBe(text);
    expect(restored?.memory_type).toBe('knowledge');
    expect(restored?.scope).toBe('project');
  });

  it('SESSION EXCLUSION: observe content stays local while durable project claims are exported', async () => {
    const sessionText = 'session-only scratchpad that must never sync';
    const projectText = 'durable project claim that should sync';

    await observeSessionContent(sessionText);
    await upsertDurableClaim({
      text: projectText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(2),
    });

    const push = await syncPush();
    expect(push.exported.claims).toBe(1);

    const exportedClaims = await readAllExportedClaims();
    expect(exportedClaims).toHaveLength(1);
    expect(exportedClaims[0]?.text).toBe(projectText);
    expect(exportedClaims.some((claim) => claim.text === sessionText)).toBe(false);
    expect(await pathExists(path.join(tempDir, SYNC_DIR_NAME, 'claims', 'session'))).toBe(false);
  });

  it('ROLLED-BACK EXCLUSION: rolled-back promoted claims are not exported', async () => {
    const { distill, promote } = await promoteObservedContent(
      'rolled-back claim should not round-trip',
      atMinutes(3)
    );

    const promotedClaim = await findClaimById(promote.claim_id);
    expect(promotedClaim?.content_hash).toBe(contentHashFor(distill.distilled_text));

    await rollbackClaim(promote.claim_id, atMinutes(4));

    const push = await syncPush();
    expect(push.exported.claims).toBe(0);
    expect(await readAllExportedClaims()).toHaveLength(0);
    expect(await pathExists(claimExportPath('project', distill.distilled_text))).toBe(false);
  });

  it('BOUNDARY UPGRADE ON MERGE: incoming stronger boundary upgrades existing durable claims', async () => {
    const text = 'same claim with stronger sender boundary';

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(5),
    });
    await syncPush();

    await resetRuntime();

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'public',
      provenanceAt: atMinutes(6),
    });

    const beforePull = await findClaimByContentHash(contentHashFor(text));
    expect(beforePull?.boundary_class).toBe('public');

    const pull = await syncPull();
    expect(pull.imported.claims.new).toBe(0);
    expect(pull.imported.claims.upgraded_boundary).toBe(1);

    const merged = await findClaimByContentHash(contentHashFor(text));
    expect(merged?.boundary_class).toBe('internal');
  });

  it('MEMORY_TYPE BACKFILL: incoming memory_type fills existing claims that are missing it', async () => {
    const text = 'receiver should backfill missing memory_type';

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(7),
    });
    await syncPush();

    await resetRuntime();

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      provenanceAt: atMinutes(8),
    });

    const beforePull = await findClaimByContentHash(contentHashFor(text));
    expect(beforePull?.memory_type).toBeNull();

    const pull = await syncPull();
    expect(pull.imported.claims.new).toBe(0);
    expect(pull.imported.claims.skipped_duplicate).toBe(1);
    expect(pull.imported.claims.upgraded_boundary).toBe(0);

    const merged = await findClaimByContentHash(contentHashFor(text));
    expect(merged?.memory_type).toBe('knowledge');
  });

  it('ENTITY+RELATION SYNC: exports and restores entities and relations linked through claim upsert', async () => {
    const text = 'claim linked to graph memory';

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(9),
      entities: [
        { id: 'ent_roundtrip_actor', type: 'Actor', name: 'Sync Agent' },
        { id: 'ent_roundtrip_concept', type: 'Concept', name: 'Round Trip' },
      ],
      relations: [
        {
          id: 'rel_roundtrip_actor_concept',
          src_id: 'ent_roundtrip_actor',
          dst_id: 'ent_roundtrip_concept',
          type: 'RELATED_TO',
        },
      ],
    });

    const push = await syncPush();
    expect(push.exported.claims).toBe(1);
    expect(push.exported.entities).toBe(2);
    expect(push.exported.relations).toBe(1);

    await resetRuntime();

    const pull = await syncPull();
    expect(pull.imported.claims.new).toBe(1);
    expect(pull.imported.entities.new).toBe(2);
    expect(pull.imported.relations.new).toBe(1);

    const restoredClaim = await findClaimByContentHash(contentHashFor(text));
    expect(restoredClaim?.text).toBe(text);
    expect((await findEntityById('ent_roundtrip_actor'))?.name).toBe('Sync Agent');
    expect((await findEntityById('ent_roundtrip_concept'))?.name).toBe('Round Trip');
    expect((await findRelationById('rel_roundtrip_actor_concept'))).toMatchObject({
      id: 'rel_roundtrip_actor_concept',
      src_id: 'ent_roundtrip_actor',
      dst_id: 'ent_roundtrip_concept',
      type: 'RELATED_TO',
    });
  });

  it('MULTI-CLAIM ROUND-TRIP: restores diverse durable claims with their metadata intact', async () => {
    const claims: DurableClaimInput[] = [
      {
        text: 'fact knowledge round-trip',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        provenanceAt: atMinutes(10),
      },
      {
        text: 'task working-state round-trip',
        kind: 'task',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'working_state',
        provenanceAt: atMinutes(11),
      },
      {
        text: 'preference procedure round-trip',
        kind: 'preference',
        scope: 'project',
        boundary_class: 'public',
        memory_type: 'procedure',
        provenanceAt: atMinutes(12),
      },
      {
        text: 'policy norm round-trip',
        kind: 'policy_hint',
        scope: 'principle',
        boundary_class: 'internal',
        memory_type: 'norm',
        provenanceAt: atMinutes(13),
      },
      {
        text: 'second fact knowledge round-trip',
        kind: 'fact',
        scope: 'project',
        boundary_class: 'public',
        memory_type: 'knowledge',
        provenanceAt: atMinutes(14),
      },
    ];

    for (const claim of claims) {
      await upsertDurableClaim(claim);
    }

    const push = await syncPush();
    expect(push.exported.claims).toBe(5);

    await resetRuntime();

    const pull = await syncPull();
    expect(pull.imported.claims.new).toBe(5);
    expect(await countClaims()).toBe(5);

    for (const expected of claims) {
      const restored = await findClaimByContentHash(contentHashFor(expected.text));
      expect(restored).toMatchObject({
        text: expected.text,
        kind: expected.kind,
        scope: expected.scope,
        boundary_class: expected.boundary_class,
        memory_type: expected.memory_type,
      });
    }
  });

  it('IDEMPOTENT PULL: repeated pulls do not duplicate claims and report zero new imports', async () => {
    const text = 'idempotent pull durable claim';

    await upsertDurableClaim({
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      memory_type: 'knowledge',
      provenanceAt: atMinutes(15),
    });
    await syncPush();

    await resetRuntime();

    const firstPull = await syncPull();
    expect(firstPull.imported.claims.new).toBe(1);
    expect(await countClaims()).toBe(1);

    const secondPull = await syncPull();
    expect(secondPull.imported.claims.new).toBe(0);
    expect(secondPull.imported.claims.skipped_duplicate).toBe(1);
    expect(await countClaims()).toBe(1);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT COUNT(*)::INTEGER AS cnt FROM claims WHERE content_hash = $1',
      [contentHashFor(text)]
    );
    const rows = reader.getRowObjects() as Array<{ cnt: number }>;
    expect(rows[0]?.cnt).toBe(1);
  });
});

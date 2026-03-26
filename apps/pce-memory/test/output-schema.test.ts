/**
 * MCP Structured Output対応テスト
 * - スキーマ整合性テスト
 * - 後方互換性テスト（content配列が常に存在）
 * - structuredContent == JSON.parse(content[0].text) の検証
 */
import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';
import { computeContentHash } from '@pce/embeddings';
import { MEMORY_TYPES } from '../src/domain/types';

// テスト前にDBと状態をリセット
beforeEach(async () => {
  await resetDbAsync();
  resetMemoryState();
  resetLayerScopeState();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  await initRateState();
  await resetRates();
});

describe('Output Schema - 基本テスト', () => {
  it('すべてのTOOL_DEFINITIONSにoutputSchemaが定義されている', () => {
    for (const tool of TOOL_DEFINITIONS) {
      expect(tool.outputSchema, `${tool.name} should have outputSchema`).toBeDefined();
      expect(tool.outputSchema?.type).toBe('object');
      expect(tool.outputSchema?.properties).toBeDefined();
      expect(tool.outputSchema?.required).toBeDefined();
    }
  });

  it('outputSchemaのrequiredプロパティがpropertiesに存在する', () => {
    for (const tool of TOOL_DEFINITIONS) {
      const schema = tool.outputSchema;
      if (schema?.required && schema?.properties) {
        for (const requiredProp of schema.required as string[]) {
          expect(
            schema.properties[requiredProp],
            `${tool.name}: required property "${requiredProp}" not in properties`
          ).toBeDefined();
        }
      }
    }
  });

  it('pce_memory_upsert inputSchema は secret boundary_class を通常入力として案内しない', () => {
    const upsertTool = TOOL_DEFINITIONS.find((tool) => tool.name === 'pce_memory_upsert');
    expect(upsertTool).toBeDefined();

    expect(upsertTool?.description).toContain('project and principle scopes');
    expect(upsertTool?.description).toContain('session claims may omit provenance');

    const boundaryClassSchema = upsertTool?.inputSchema?.properties?.boundary_class as
      | { enum?: string[]; description?: string }
      | undefined;
    const memoryTypeSchema = upsertTool?.inputSchema?.properties?.memory_type as
      | { enum?: string[]; description?: string }
      | undefined;
    const provenanceSchema = upsertTool?.inputSchema?.properties?.provenance as
      | {
          description?: string;
          properties?: { at?: { description?: string } };
          required?: string[];
        }
      | undefined;
    expect(boundaryClassSchema?.enum).toEqual(['public', 'internal', 'pii']);
    expect(boundaryClassSchema?.description).toContain('secret is rejected by default');
    expect(boundaryClassSchema?.description).toContain('pce_memory_observe');
    expect(memoryTypeSchema?.enum).toEqual([...MEMORY_TYPES]);
    expect(memoryTypeSchema?.description).toContain('Optional v2 memory taxonomy');
    expect(provenanceSchema?.description).toContain('Optional for session scope');
    expect(provenanceSchema?.properties?.at?.description).toContain(
      'Required for project and principle scopes'
    );

    // allOf/anyOf are not used (Claude API does not support them at top level)
    expect(upsertTool?.inputSchema?.allOf).toBeUndefined();
  });
});

describe('Output Schema - 後方互換性テスト', () => {
  it('pce_memory_policy_apply: contentとstructuredContentの両方が返される', async () => {
    const result = await dispatchTool('pce_memory_policy_apply', {});

    // 後方互換性: content配列は常に存在
    expect(result.content).toBeDefined();
    expect(Array.isArray(result.content)).toBe(true);
    expect(result.content.length).toBeGreaterThan(0);
    expect(result.content[0].type).toBe('text');

    // 新機能: structuredContentも存在
    expect(result.structuredContent).toBeDefined();

    // 整合性: 両方のデータが一致
    const contentData = JSON.parse(result.content[0].text);
    expect(result.structuredContent).toEqual(contentData);
  });

  it('pce_memory_state: contentとstructuredContentの両方が返される', async () => {
    const result = await dispatchTool('pce_memory_state', {});

    expect(result.content).toBeDefined();
    expect(result.structuredContent).toBeDefined();

    const contentData = JSON.parse(result.content[0].text);
    expect(result.structuredContent).toEqual(contentData);
  });
});

describe('Output Schema - ハンドラ出力検証', () => {
  it('pce_memory_policy_apply: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce_memory_policy_apply', {});
    const data = result.structuredContent!;

    // 必須フィールドの存在確認
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_upsert: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyを実行
    await dispatchTool('pce_memory_policy_apply', {});

    const text = 'テスト知識';
    const result = await dispatchTool('pce_memory_upsert', {
      text,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(text)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const data = result.structuredContent!;

    expect(data.id).toBeDefined();
    expect(typeof data.is_new).toBe('boolean');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_activate: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとupsertを実行
    await dispatchTool('pce_memory_policy_apply', {});
    const activateText = 'テスト知識activate';
    await dispatchTool('pce_memory_upsert', {
      text: activateText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(activateText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    const result = await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
    });
    const data = result.structuredContent!;

    expect(data.active_context_id).toBeDefined();
    expect(Array.isArray(data.claims)).toBe(true);
    expect(data.claims[0]?.source).toBeDefined();
    expect(typeof data.claims_count).toBe('number');
    expect(typeof data.has_more).toBe('boolean');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_graph_audit: 出力がスキーマに準拠', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const result = await dispatchTool('pce_memory_graph_audit', {});
    const data = result.structuredContent! as {
      summary: { claims: number };
      truncation: { claims: boolean; entities: boolean; relations: boolean };
      findings: unknown[];
      components: unknown[];
      policy_version: string;
      state: string;
      request_id: string;
      trace_id: string;
    };

    expect(data.summary).toBeDefined();
    expect(typeof data.summary.truncated === 'boolean' || data.summary.truncated === undefined).toBe(
      true
    );
    expect(typeof data.truncation.claims).toBe('boolean');
    expect(typeof data.truncation.entities).toBe('boolean');
    expect(typeof data.truncation.relations).toBe('boolean');
    expect(Array.isArray(data.findings)).toBe(true);
    expect(Array.isArray(data.components)).toBe(true);
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_rollback: blast_radius が topology shape を返す', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const rootText = 'rollback schema root';
    const supportText = 'rollback schema support';
    const root = await dispatchTool('pce_memory_upsert', {
      text: rootText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(rootText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const support = await dispatchTool('pce_memory_upsert', {
      text: supportText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(supportText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    await dispatchTool('pce_memory_link_claims', {
      source_claim_id: support.structuredContent!.id as string,
      target_claim_id: root.structuredContent!.id as string,
      link_type: 'supports',
    });
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
      q: rootText,
      top_k: 5,
    });

    const result = await dispatchTool('pce_memory_rollback', {
      claim_id: root.structuredContent!.id as string,
      reason: 'schema rollback',
      provenance: { at: '2025-01-01T00:00:05.000Z', actor: 'vitest' },
    });
    const data = result.structuredContent! as {
      blast_radius: {
        scope: string;
        target_layer: string;
        root_claim: { id: string };
        connected_claims: Array<{ claim: { id: string } }>;
        linked_entities: unknown[];
        affected_active_contexts: Array<{ active_context_id: string }>;
        neighborhoods: Record<string, unknown>;
        summary: { connected_claims: number };
      };
    };

    expect(data.blast_radius.scope).toBe('project');
    expect(data.blast_radius.target_layer).toBe('meso');
    expect(data.blast_radius.root_claim.id).toBe(root.structuredContent!.id);
    expect(data.blast_radius.connected_claims).toEqual(
      expect.arrayContaining([
        expect.objectContaining({
          claim: expect.objectContaining({ id: support.structuredContent!.id }),
        }),
      ])
    );
    expect(Array.isArray(data.blast_radius.linked_entities)).toBe(true);
    expect(Array.isArray(data.blast_radius.affected_active_contexts)).toBe(true);
    expect(data.blast_radius.neighborhoods).toBeDefined();
    expect(data.blast_radius.summary.connected_claims).toBeGreaterThanOrEqual(1);
  });

  it('pce_memory_boundary_validate: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce_memory_boundary_validate', {
      payload: 'テストペイロード',
    });
    const data = result.structuredContent!;

    expect(typeof data.allowed).toBe('boolean');
    // redactedは条件によっては存在しない場合がある
    expect(data.policy_version).toBeDefined();
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_feedback: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとupsertを実行してclaimを作成
    await dispatchTool('pce_memory_policy_apply', {});
    const feedbackText = 'テスト知識feedback';
    const upsertResult = await dispatchTool('pce_memory_upsert', {
      text: feedbackText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(feedbackText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const claimId = upsertResult.structuredContent!.id as string;

    // activateしてReady状態にする
    await dispatchTool('pce_memory_activate', {
      scope: ['project'],
      allow: ['answer:task'],
    });

    const result = await dispatchTool('pce_memory_feedback', {
      claim_id: claimId,
      signal: 'helpful',
    });
    const data = result.structuredContent!;

    expect(data.id).toBeDefined();
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_state: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce_memory_state', {});
    const data = result.structuredContent!;

    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.policy_version).toBeDefined();
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_upsert_entity: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyを実行
    await dispatchTool('pce_memory_policy_apply', {});

    const result = await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_test_001',
      type: 'Concept',
      name: 'テストエンティティ',
    });
    const data = result.structuredContent!;

    expect(data.id).toBe('ent_test_001');
    expect(data.type).toBe('Concept');
    expect(data.name).toBe('テストエンティティ');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_link_claims: 出力がスキーマに準拠', async () => {
    await dispatchTool('pce_memory_policy_apply', {});

    const sourceText = 'schema link source';
    const targetText = 'schema link target';
    const source = await dispatchTool('pce_memory_upsert', {
      text: sourceText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(sourceText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });
    const target = await dispatchTool('pce_memory_upsert', {
      text: targetText,
      kind: 'fact',
      scope: 'project',
      boundary_class: 'internal',
      content_hash: `sha256:${computeContentHash(targetText)}`,
      provenance: { at: '2025-01-01T00:00:00.000Z' },
    });

    const result = await dispatchTool('pce_memory_link_claims', {
      source_claim_id: source.structuredContent!.id as string,
      target_claim_id: target.structuredContent!.id as string,
      link_type: 'related',
    });
    const data = result.structuredContent!;

    expect(data.id).toBeDefined();
    expect(typeof data.is_new).toBe('boolean');
    expect(data.source_claim_id).toBeDefined();
    expect(data.target_claim_id).toBeDefined();
    expect(data.link_type).toBe('related');
    expect(typeof data.confidence).toBe('number');
    expect(data.created_by).toBe('client');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_upsert_relation: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとエンティティを作成
    await dispatchTool('pce_memory_policy_apply', {});
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_src',
      type: 'Concept',
      name: 'ソースエンティティ',
    });
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_dst',
      type: 'Concept',
      name: 'ターゲットエンティティ',
    });

    const result = await dispatchTool('pce_memory_upsert_relation', {
      id: 'rel_test_001',
      src_id: 'ent_src',
      dst_id: 'ent_dst',
      type: 'RELATES_TO',
    });
    const data = result.structuredContent!;

    expect(data.id).toBe('rel_test_001');
    expect(data.src_id).toBe('ent_src');
    expect(data.dst_id).toBe('ent_dst');
    expect(data.type).toBe('RELATES_TO');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_query_entity: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとエンティティを作成
    await dispatchTool('pce_memory_policy_apply', {});
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_query_test',
      type: 'Concept',
      name: 'クエリテストエンティティ',
    });

    const result = await dispatchTool('pce_memory_query_entity', {
      type: 'Concept',
    });
    const data = result.structuredContent!;

    expect(Array.isArray(data.entities)).toBe(true);
    expect(typeof data.count).toBe('number');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce_memory_query_relation: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとリレーションを作成
    await dispatchTool('pce_memory_policy_apply', {});
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_rel_src',
      type: 'Actor',
      name: 'リレーションソース',
    });
    await dispatchTool('pce_memory_upsert_entity', {
      id: 'ent_rel_dst',
      type: 'Artifact',
      name: 'リレーションターゲット',
    });
    await dispatchTool('pce_memory_upsert_relation', {
      id: 'rel_query_test',
      src_id: 'ent_rel_src',
      dst_id: 'ent_rel_dst',
      type: 'CREATED',
    });

    const result = await dispatchTool('pce_memory_query_relation', {
      type: 'CREATED',
    });
    const data = result.structuredContent!;

    expect(Array.isArray(data.relations)).toBe(true);
    expect(typeof data.count).toBe('number');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });
});

describe('Property: structuredContent整合性', () => {
  it('Property: contentとstructuredContentは常に同一データを表現する', async () => {
    // policy.applyを実行
    const result = await dispatchTool('pce_memory_policy_apply', {});

    // contentをパースしてstructuredContentと比較
    const parsedContent = JSON.parse(result.content[0].text);

    // 両者が同一であることを検証
    expect(result.structuredContent).toEqual(parsedContent);
  });
});

describe('Output Schema - エラー時の出力', () => {
  it('バリデーションエラー時もcontent配列が存在しisErrorがtrue', async () => {
    // policy.applyなしでupsertを実行（STATE_ERROR）
    const result = await dispatchTool('pce_memory_upsert', {
      text: 'テスト',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '3'.repeat(64),
    });

    // エラー時もcontent配列は存在
    expect(result.content).toBeDefined();
    expect(result.isError).toBe(true);

    // エラー時もstructuredContentが存在（エラー情報を含む）
    expect(result.structuredContent).toBeDefined();
    // エラー構造は { error: { code, message }, request_id, trace_id }
    const errorData = result.structuredContent as { error: { code: string; message: string } };
    expect(errorData.error).toBeDefined();
    expect(errorData.error.code).toBeDefined();
    expect(errorData.error.message).toBeDefined();
  });
});

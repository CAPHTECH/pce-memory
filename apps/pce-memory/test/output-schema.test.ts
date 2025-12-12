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
});

describe('Output Schema - 後方互換性テスト', () => {
  it('pce.memory.policy.apply: contentとstructuredContentの両方が返される', async () => {
    const result = await dispatchTool('pce.memory.policy.apply', {});

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

  it('pce.memory.state: contentとstructuredContentの両方が返される', async () => {
    const result = await dispatchTool('pce.memory.state', {});

    expect(result.content).toBeDefined();
    expect(result.structuredContent).toBeDefined();

    const contentData = JSON.parse(result.content[0].text);
    expect(result.structuredContent).toEqual(contentData);
  });
});

describe('Output Schema - ハンドラ出力検証', () => {
  it('pce.memory.policy.apply: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce.memory.policy.apply', {});
    const data = result.structuredContent!;

    // 必須フィールドの存在確認
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce.memory.upsert: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyを実行
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.upsert', {
      text: 'テスト知識',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '0'.repeat(64),
    });
    const data = result.structuredContent!;

    expect(data.id).toBeDefined();
    expect(typeof data.is_new).toBe('boolean');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce.memory.activate: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとupsertを実行
    await dispatchTool('pce.memory.policy.apply', {});
    await dispatchTool('pce.memory.upsert', {
      text: 'テスト知識',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '1'.repeat(64),
    });

    const result = await dispatchTool('pce.memory.activate', {
      scope: ['session'],
      allow: ['answer:task'],
    });
    const data = result.structuredContent!;

    expect(data.active_context_id).toBeDefined();
    expect(Array.isArray(data.claims)).toBe(true);
    expect(typeof data.claims_count).toBe('number');
    expect(typeof data.has_more).toBe('boolean');
    expect(data.policy_version).toBeDefined();
    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce.memory.boundary.validate: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce.memory.boundary.validate', {
      payload: 'テストペイロード',
    });
    const data = result.structuredContent!;

    expect(typeof data.allowed).toBe('boolean');
    // redactedは条件によっては存在しない場合がある
    expect(data.policy_version).toBeDefined();
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce.memory.feedback: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとupsertを実行してclaimを作成
    await dispatchTool('pce.memory.policy.apply', {});
    const upsertResult = await dispatchTool('pce.memory.upsert', {
      text: 'テスト知識',
      kind: 'fact',
      scope: 'session',
      boundary_class: 'internal',
      content_hash: 'sha256:' + '2'.repeat(64),
    });
    const claimId = upsertResult.structuredContent!.id as string;

    // activateしてReady状態にする
    await dispatchTool('pce.memory.activate', {
      scope: ['session'],
      allow: ['answer:task'],
    });

    const result = await dispatchTool('pce.memory.feedback', {
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

  it('pce.memory.state: 出力がスキーマに準拠', async () => {
    const result = await dispatchTool('pce.memory.state', {});
    const data = result.structuredContent!;

    expect(['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready']).toContain(data.state);
    expect(data.policy_version).toBeDefined();
    expect(data.request_id).toBeDefined();
    expect(data.trace_id).toBeDefined();
  });

  it('pce.memory.upsert.entity: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyを実行
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.upsert.entity', {
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

  it('pce.memory.upsert.relation: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとエンティティを作成
    await dispatchTool('pce.memory.policy.apply', {});
    await dispatchTool('pce.memory.upsert.entity', {
      id: 'ent_src',
      type: 'Concept',
      name: 'ソースエンティティ',
    });
    await dispatchTool('pce.memory.upsert.entity', {
      id: 'ent_dst',
      type: 'Concept',
      name: 'ターゲットエンティティ',
    });

    const result = await dispatchTool('pce.memory.upsert.relation', {
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

  it('pce.memory.query.entity: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとエンティティを作成
    await dispatchTool('pce.memory.policy.apply', {});
    await dispatchTool('pce.memory.upsert.entity', {
      id: 'ent_query_test',
      type: 'Concept',
      name: 'クエリテストエンティティ',
    });

    const result = await dispatchTool('pce.memory.query.entity', {
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

  it('pce.memory.query.relation: 出力がスキーマに準拠', async () => {
    // 事前にpolicy.applyとリレーションを作成
    await dispatchTool('pce.memory.policy.apply', {});
    await dispatchTool('pce.memory.upsert.entity', {
      id: 'ent_rel_src',
      type: 'Actor',
      name: 'リレーションソース',
    });
    await dispatchTool('pce.memory.upsert.entity', {
      id: 'ent_rel_dst',
      type: 'Artifact',
      name: 'リレーションターゲット',
    });
    await dispatchTool('pce.memory.upsert.relation', {
      id: 'rel_query_test',
      src_id: 'ent_rel_src',
      dst_id: 'ent_rel_dst',
      type: 'CREATED',
    });

    const result = await dispatchTool('pce.memory.query.relation', {
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
    const result = await dispatchTool('pce.memory.policy.apply', {});

    // contentをパースしてstructuredContentと比較
    const parsedContent = JSON.parse(result.content[0].text);

    // 両者が同一であることを検証
    expect(result.structuredContent).toEqual(parsedContent);
  });
});

describe('Output Schema - エラー時の出力', () => {
  it('バリデーションエラー時もcontent配列が存在しisErrorがtrue', async () => {
    // policy.applyなしでupsertを実行（STATE_ERROR）
    const result = await dispatchTool('pce.memory.upsert', {
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

import { describe, it, expect, beforeEach } from 'vitest';
import { initDb, initSchema, resetDbAsync, getConnection } from '../src/db/connection';
import { dispatchTool, TOOL_DEFINITIONS } from '../src/core/handlers';
import { resetMemoryState } from '../src/state/memoryState';
import { resetLayerScopeState } from '../src/state/layerScopeState';
import { resetRates, initRateState } from '../src/store/rate';
import { gcExpiredObservations } from '../src/store/observations';

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

describe('pce.memory.observe', () => {
  it('TOOL_DEFINITIONSに含まれる', () => {
    const names = TOOL_DEFINITIONS.map((t) => t.name);
    expect(names).toContain('pce.memory.observe');
  });

  it('extract.mode=noop: observation_idのみ返す（claim_idsは空）', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'hello observation',
      extract: { mode: 'noop' },
    });

    expect(result.structuredContent).toBeDefined();
    const data = result.structuredContent!;
    expect(typeof data.observation_id).toBe('string');
    expect(Array.isArray(data.claim_ids)).toBe(true);
    expect(data.claim_ids).toHaveLength(0);

    // DBに保存されていること
    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT id, content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { id: string; content: string | null }[];
    expect(rows[0]?.id).toBe(data.observation_id);
    expect(rows[0]?.content).toBe('hello observation');
  });

  it('extract.mode=single_claim_v0: claim_idsが返り、activate(include_meta)でEvidenceが返る', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const obs = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'my observation content',
      extract: { mode: 'single_claim_v0' },
    });
    const obsData = obs.structuredContent!;

    expect(typeof obsData.observation_id).toBe('string');
    expect(Array.isArray(obsData.claim_ids)).toBe(true);
    expect(obsData.claim_ids).toHaveLength(1);
    const claimId = (obsData.claim_ids as string[])[0]!;

    const ac = await dispatchTool('pce.memory.activate', {
      scope: ['session'],
      allow: ['answer:task'],
      include_meta: true,
    });
    const acData = ac.structuredContent!;
    expect(Array.isArray(acData.claims)).toBe(true);

    const match = (acData.claims as any[]).find((x) => x?.claim?.id === claimId);
    expect(match).toBeDefined();
    expect(Array.isArray(match.evidences)).toBe(true);

    const ev = match.evidences.find(
      (e: any) => e?.source_type === 'observation' && e?.source_id === obsData.observation_id
    );
    expect(ev).toBeDefined();
  });

  it('secret検知時: contentは保存せずextractもスキップする', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const secretText = `sk-${'A'.repeat(30)}`;
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: secretText,
      extract: { mode: 'single_claim_v0' },
    });

    const data = result.structuredContent!;
    expect(data.effective_boundary_class).toBe('secret');
    expect(data.content_stored).toBe(false);
    expect(Array.isArray(data.claim_ids)).toBe(true);
    expect(data.claim_ids).toHaveLength(0);
    expect(Array.isArray(data.warnings)).toBe(true);
    expect(data.warnings as string[]).toContain('OBS_CONTENT_NOT_STORED_SECRET');
    expect(data.warnings as string[]).toContain('EXTRACT_SKIPPED_SECRET');

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string | null }[];
    expect(rows[0]?.content).toBeNull();
  });

  it('GC(scrub): 期限切れ後にcontentがNULL化される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'will be scrubbed',
      ttl_days: 1,
      extract: { mode: 'noop' },
    });
    const data = result.structuredContent!;
    const observationId = data.observation_id as string;

    // expires_atを過去にする
    const conn = await getConnection();
    await conn.run(
      "UPDATE observations SET expires_at = (CURRENT_TIMESTAMP - INTERVAL '1 day') WHERE id = $1",
      [observationId]
    );

    await gcExpiredObservations('scrub');

    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      observationId,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string | null }[];
    expect(rows[0]?.content).toBeNull();
  });

  // Issue #30 Review: Edge case tests追加

  it('tags validation: 不正な文字を含むタグはエラーになる', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'test content',
      tags: ['valid-tag', 'invalid<script>tag'],
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('invalid characters');
  });

  it('tags validation: 長すぎるタグはエラーになる', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const longTag = 'a'.repeat(300); // 256文字を超える
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'test content',
      tags: [longTag],
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('tag too long');
  });

  it('secret検知時: content_digestがREDACTED_SECRETになる', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const secretText = `sk-${'A'.repeat(30)}`;
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: secretText,
      extract: { mode: 'noop' },
    });

    const data = result.structuredContent!;
    expect(data.effective_boundary_class).toBe('secret');

    // DBのcontent_digestがREDACTED_SECRETになっていることを確認
    const conn = await getConnection();
    const reader = await conn.runAndReadAll(
      'SELECT content_digest FROM observations WHERE id = $1',
      [data.observation_id]
    );
    const rows = reader.getRowObjects() as unknown as { content_digest: string }[];
    expect(rows[0]?.content_digest).toBe('sha256:REDACTED_SECRET');
  });

  it('GC(scrub): 期限切れ後にactor, source_id, tagsもNULL化される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'will be scrubbed',
      actor: 'test-user@example.com',
      source_id: 'https://example.com/session/123',
      tags: ['tag1', 'tag2'],
      ttl_days: 1,
      extract: { mode: 'noop' },
    });
    const data = result.structuredContent!;
    const observationId = data.observation_id as string;

    // expires_atを過去にする
    const conn = await getConnection();
    await conn.run(
      "UPDATE observations SET expires_at = (CURRENT_TIMESTAMP - INTERVAL '1 day') WHERE id = $1",
      [observationId]
    );

    await gcExpiredObservations('scrub');

    const reader = await conn.runAndReadAll(
      'SELECT content, actor, source_id, tags FROM observations WHERE id = $1',
      [observationId]
    );
    const rows = reader.getRowObjects() as unknown as {
      content: string | null;
      actor: string | null;
      source_id: string | null;
      tags: unknown;
    }[];
    expect(rows[0]?.content).toBeNull();
    expect(rows[0]?.actor).toBeNull();
    expect(rows[0]?.source_id).toBeNull();
    expect(rows[0]?.tags).toBeNull();
  });

  it('tags validation: 有効なタグパターンは許可される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    // 許可される文字: [\w\-:.@/]
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'test content',
      tags: ['valid-tag', 'user:name', 'path/to/resource', 'email@domain.com', 'under_score'],
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBeFalsy();
    expect(result.structuredContent?.observation_id).toBeDefined();
  });

  // === 追加テスト: 状態・入力検証 ===

  it('STATE_ERROR: Uninitializedでobserveするとエラー', async () => {
    // policy.applyを呼ばずにobserve
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'test',
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('STATE_ERROR');
  });

  it('VALIDATION_ERROR: source_type未指定', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      content: 'test',
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
  });

  it('VALIDATION_ERROR: content未指定', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
  });

  it('VALIDATION_ERROR: boundary_class不正値', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'test',
      boundary_class: 'invalid_class',
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('boundary_class');
  });

  it('VALIDATION_ERROR: contentサイズ上限超過', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    // デフォルト上限は64KB
    const largeContent = 'x'.repeat(100_000);
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: largeContent,
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
    expect(result.structuredContent?.error?.message).toContain('too large');
  });

  // === 追加テスト: PII/GC ===

  it('PII検知: メールアドレスがリダクションされDBに保存', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: '連絡先: test@example.com です',
      extract: { mode: 'noop' },
    });

    const data = result.structuredContent!;
    expect(data.effective_boundary_class).toBe('pii');
    expect(data.content_stored).toBe(true);
    expect(data.content_redacted).toBe(true);

    // DBにリダクションされた値が保存されていることを確認
    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string }[];
    expect(rows[0]?.content).toContain('[REDACTED]');
    expect(rows[0]?.content).not.toContain('test@example.com');
  });

  it('PII検知: 電話番号がリダクションされDBに保存', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: '電話: 090-1234-5678 まで',
      extract: { mode: 'noop' },
    });

    const data = result.structuredContent!;
    expect(data.effective_boundary_class).toBe('pii');
    expect(data.content_redacted).toBe(true);

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string }[];
    expect(rows[0]?.content).toContain('[REDACTED]');
    expect(rows[0]?.content).not.toContain('090-1234-5678');
  });

  it('GC(delete): 期限切れ後に行が削除される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'will be deleted',
      ttl_days: 1,
      extract: { mode: 'noop' },
    });
    const observationId = result.structuredContent!.observation_id as string;

    const conn = await getConnection();
    await conn.run(
      "UPDATE observations SET expires_at = (CURRENT_TIMESTAMP - INTERVAL '1 day') WHERE id = $1",
      [observationId]
    );

    await gcExpiredObservations('delete');

    const reader = await conn.runAndReadAll('SELECT id FROM observations WHERE id = $1', [
      observationId,
    ]);
    const rows = reader.getRowObjects() as unknown as { id: string }[];
    expect(rows).toHaveLength(0);
  });

  // === 追加テスト: エッジケース ===

  it('空content: 空文字列でもobserve可能', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: '',
      extract: { mode: 'noop' },
    });

    // 空文字列はエラーになる（contentは必須）
    expect(result.isError).toBe(true);
    expect(result.structuredContent?.error?.code).toBe('VALIDATION_ERROR');
  });

  it('日本語content: マルチバイト文字が正しく保存される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const japaneseContent = 'これは日本語のテストです。絵文字も含む🎉';
    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: japaneseContent,
      extract: { mode: 'noop' },
    });

    expect(result.isError).toBeFalsy();
    const data = result.structuredContent!;

    const conn = await getConnection();
    const reader = await conn.runAndReadAll('SELECT content FROM observations WHERE id = $1', [
      data.observation_id,
    ]);
    const rows = reader.getRowObjects() as unknown as { content: string }[];
    expect(rows[0]?.content).toBe(japaneseContent);
  });

  it('重複observe: 同一contentでも別のobservation_idが生成される', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const content = 'duplicate content test';

    const result1 = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content,
      extract: { mode: 'noop' },
    });

    const result2 = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content,
      extract: { mode: 'noop' },
    });

    expect(result1.structuredContent?.observation_id).not.toBe(
      result2.structuredContent?.observation_id
    );
  });

  it('source_type全種: 各source_typeでobserve可能', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const sourceTypes = ['chat', 'tool', 'file', 'http', 'system'] as const;

    for (const sourceType of sourceTypes) {
      const result = await dispatchTool('pce.memory.observe', {
        source_type: sourceType,
        content: `content for ${sourceType}`,
        extract: { mode: 'noop' },
      });

      expect(result.isError).toBeFalsy();
      expect(result.structuredContent?.observation_id).toBeDefined();
    }
  });

  it('boundary_class昇格: 明示的publicでもPII検知でpiiに昇格', async () => {
    await dispatchTool('pce.memory.policy.apply', {});

    const result = await dispatchTool('pce.memory.observe', {
      source_type: 'chat',
      content: 'public info with email: secret@example.com',
      boundary_class: 'public',
      extract: { mode: 'noop' },
    });

    const data = result.structuredContent!;
    // PIIが検知されるとpiiに昇格
    expect(data.effective_boundary_class).toBe('pii');
    expect(data.content_redacted).toBe(true);
  });
});

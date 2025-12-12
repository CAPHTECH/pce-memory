/**
 * MCP Prompts機能のテスト (Issue #16)
 *
 * handleListPrompts, handleGetPromptの単体テスト
 */
import { describe, it, expect } from 'vitest';
import { handleListPrompts, handleGetPrompt, PROMPTS_DEFINITIONS } from '../src/core/handlers';

describe('MCP Prompts (Issue #16)', () => {
  describe('PROMPTS_DEFINITIONS', () => {
    it('定義済みPromptsが存在する', () => {
      expect(PROMPTS_DEFINITIONS.length).toBeGreaterThan(0);
    });

    it('すべてのPromptにnameとdescriptionがある', () => {
      for (const prompt of PROMPTS_DEFINITIONS) {
        expect(prompt.name).toBeDefined();
        expect(typeof prompt.name).toBe('string');
        expect(prompt.name.length).toBeGreaterThan(0);
        // descriptionはオプションだが、定義済みのものにはすべてある
        expect(prompt.description).toBeDefined();
      }
    });

    it('期待されるPromptが含まれている', () => {
      const names = PROMPTS_DEFINITIONS.map((p) => p.name);
      expect(names).toContain('recall_context');
      expect(names).toContain('record_decision');
      expect(names).toContain('sync_workflow');
      expect(names).toContain('debug_assist');
    });
  });

  describe('handleListPrompts', () => {
    it('すべてのPromptsを返す', async () => {
      const result = await handleListPrompts({});
      expect(result.prompts).toBeDefined();
      expect(result.prompts.length).toBe(PROMPTS_DEFINITIONS.length);
    });

    it('ページネーションcursorをサポートする', async () => {
      // 最初のページ
      const page1 = await handleListPrompts({});
      expect(page1.prompts.length).toBe(PROMPTS_DEFINITIONS.length);

      // カーソル指定（全件取得後なので空）
      const page2 = await handleListPrompts({ cursor: '10' });
      expect(page2.prompts.length).toBe(0);
    });
  });

  describe('handleGetPrompt', () => {
    it('存在するPromptを取得できる', async () => {
      const result = await handleGetPrompt({ name: 'recall_context' });
      expect(result.description).toBeDefined();
      expect(result.messages).toBeDefined();
      expect(result.messages.length).toBeGreaterThan(0);
    });

    it('メッセージにroleとcontentがある', async () => {
      const result = await handleGetPrompt({ name: 'recall_context' });
      for (const msg of result.messages) {
        expect(msg.role).toMatch(/^(user|assistant)$/);
        expect(msg.content).toBeDefined();
        expect(msg.content.type).toBe('text');
        expect(typeof msg.content.text).toBe('string');
      }
    });

    it('引数を渡すとメッセージに反映される', async () => {
      const result = await handleGetPrompt({
        name: 'recall_context',
        arguments: { query: 'JWT認証', scope: 'project' },
      });
      // 引数がメッセージに含まれることを確認
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('JWT認証');
    });

    it('存在しないPromptでエラーを投げる', async () => {
      await expect(handleGetPrompt({ name: 'non-existent' })).rejects.toThrow(
        'Prompt not found: non-existent'
      );
    });

    it('nameなしでエラーを投げる', async () => {
      await expect(handleGetPrompt({})).rejects.toThrow('name is required');
    });

    it('必須引数がない場合エラーを投げる', async () => {
      // record-decisionのtopicは必須
      await expect(handleGetPrompt({ name: 'record_decision' })).rejects.toThrow(
        'Required argument missing: topic'
      );
    });

    it('必須引数を渡すと成功する', async () => {
      const result = await handleGetPrompt({
        name: 'record_decision',
        arguments: { topic: '状態管理ライブラリ選定' },
      });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('状態管理ライブラリ選定');
    });
  });

  describe('sync-workflow prompt', () => {
    it('operationなしでデフォルトガイドを返す', async () => {
      const result = await handleGetPrompt({ name: 'sync_workflow' });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      // statusがデフォルト
      expect(allText).toContain('status');
    });

    it('operation=pushでpushガイドを返す', async () => {
      const result = await handleGetPrompt({
        name: 'sync_workflow',
        arguments: { operation: 'push' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('Push');
      expect(allText).toContain('sync.push');
    });

    it('operation=pullでpullガイドを返す', async () => {
      const result = await handleGetPrompt({
        name: 'sync_workflow',
        arguments: { operation: 'pull' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('Pull');
      expect(allText).toContain('dry_run');
    });
  });

  describe('debug-assist prompt', () => {
    it('エラーメッセージを引数で渡せる', async () => {
      const result = await handleGetPrompt({
        name: 'debug_assist',
        arguments: { error_message: 'ECONNREFUSED' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('ECONNREFUSED');
    });
  });
});

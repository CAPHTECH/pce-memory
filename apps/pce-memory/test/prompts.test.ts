/**
 * MCP Prompts tests (Issue #16)
 *
 * Unit tests for handleListPrompts, handleGetPrompt
 */
import { describe, it, expect } from 'vitest';
import { handleListPrompts, handleGetPrompt, PROMPTS_DEFINITIONS } from '../src/core/handlers';

describe('MCP Prompts (Issue #16)', () => {
  describe('PROMPTS_DEFINITIONS', () => {
    it('has defined prompts', () => {
      expect(PROMPTS_DEFINITIONS.length).toBeGreaterThan(0);
    });

    it('all prompts have name and description', () => {
      for (const prompt of PROMPTS_DEFINITIONS) {
        expect(prompt.name).toBeDefined();
        expect(typeof prompt.name).toBe('string');
        expect(prompt.name.length).toBeGreaterThan(0);
        // description is optional but all defined prompts have it
        expect(prompt.description).toBeDefined();
      }
    });

    it('contains expected prompts', () => {
      const names = PROMPTS_DEFINITIONS.map((p) => p.name);
      expect(names).toContain('recall_context');
      expect(names).toContain('record_decision');
      expect(names).toContain('sync_workflow');
      expect(names).toContain('sync_push');
      expect(names).toContain('sync_pull');
      expect(names).toContain('debug_assist');
    });
  });

  describe('handleListPrompts', () => {
    it('returns all prompts', async () => {
      const result = await handleListPrompts({});
      expect(result.prompts).toBeDefined();
      expect(result.prompts.length).toBe(PROMPTS_DEFINITIONS.length);
    });

    it('supports pagination cursor', async () => {
      // First page
      const page1 = await handleListPrompts({});
      expect(page1.prompts.length).toBe(PROMPTS_DEFINITIONS.length);

      // Cursor specified (empty after getting all)
      const page2 = await handleListPrompts({ cursor: '10' });
      expect(page2.prompts.length).toBe(0);
    });
  });

  describe('handleGetPrompt', () => {
    it('retrieves existing prompt', async () => {
      const result = await handleGetPrompt({ name: 'recall_context' });
      expect(result.description).toBeDefined();
      expect(result.messages).toBeDefined();
      expect(result.messages.length).toBeGreaterThan(0);
    });

    it('messages have role and content', async () => {
      const result = await handleGetPrompt({ name: 'recall_context' });
      for (const msg of result.messages) {
        expect(msg.role).toMatch(/^(user|assistant)$/);
        expect(msg.content).toBeDefined();
        expect(msg.content.type).toBe('text');
        expect(typeof msg.content.text).toBe('string');
      }
    });

    it('reflects arguments in messages', async () => {
      const result = await handleGetPrompt({
        name: 'recall_context',
        arguments: { query: 'JWT authentication', scope: 'project' },
      });
      // Verify arguments are included in message
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('JWT authentication');
    });

    it('throws error for non-existent prompt', async () => {
      await expect(handleGetPrompt({ name: 'non-existent' })).rejects.toThrow(
        'Prompt not found: non-existent'
      );
    });

    it('throws error without name', async () => {
      await expect(handleGetPrompt({})).rejects.toThrow('name is required');
    });

    it('throws error when required argument is missing', async () => {
      // topic is required for record-decision
      await expect(handleGetPrompt({ name: 'record_decision' })).rejects.toThrow(
        'Required argument missing: topic'
      );
    });

    it('succeeds with required arguments', async () => {
      const result = await handleGetPrompt({
        name: 'record_decision',
        arguments: { topic: 'state management library selection' },
      });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('state management library selection');
    });
  });

  describe('sync_workflow prompt', () => {
    it('returns default guide without operation', async () => {
      const result = await handleGetPrompt({ name: 'sync_workflow' });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      // status is default
      expect(allText).toContain('status');
    });

    it('returns push guide with operation=push', async () => {
      const result = await handleGetPrompt({
        name: 'sync_workflow',
        arguments: { operation: 'push' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('Push');
      expect(allText).toContain('pce_memory_sync_push');
    });

    it('returns pull guide with operation=pull', async () => {
      const result = await handleGetPrompt({
        name: 'sync_workflow',
        arguments: { operation: 'pull' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('Pull');
      expect(allText).toContain('dry_run');
    });
  });

  describe('sync_push prompt', () => {
    it('returns push guide with default filters', async () => {
      const result = await handleGetPrompt({ name: 'sync_push' });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('pce_memory_sync_push');
      expect(allText).toContain('scope_filter');
      expect(allText).toContain('boundary_filter');
    });

    it('reflects custom filters in messages', async () => {
      const result = await handleGetPrompt({
        name: 'sync_push',
        arguments: { scope_filter: 'session,project', boundary_filter: 'public' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('session');
      expect(allText).toContain('project');
      expect(allText).toContain('public');
    });
  });

  describe('sync_pull prompt', () => {
    it('returns pull guide with dry_run recommendation', async () => {
      const result = await handleGetPrompt({ name: 'sync_pull' });
      expect(result.messages.length).toBeGreaterThan(0);
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('pce_memory_sync_pull');
      expect(allText).toContain('dry_run');
      expect(allText).toContain('CRDT');
    });

    it('includes since parameter when provided', async () => {
      const result = await handleGetPrompt({
        name: 'sync_pull',
        arguments: { since: '2024-01-01T00:00:00Z' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('2024-01-01T00:00:00Z');
    });
  });

  describe('debug_assist prompt', () => {
    it('accepts error_message as argument', async () => {
      const result = await handleGetPrompt({
        name: 'debug_assist',
        arguments: { error_message: 'ECONNREFUSED' },
      });
      const allText = result.messages.map((m) => m.content.text).join(' ');
      expect(allText).toContain('ECONNREFUSED');
    });
  });
});

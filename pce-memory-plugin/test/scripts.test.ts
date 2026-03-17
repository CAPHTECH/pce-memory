import { execFileSync } from 'node:child_process';
import { existsSync, mkdtempSync, readFileSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { afterEach, describe, expect, it } from 'vitest';

const pluginRoot = resolve(process.cwd(), 'pce-memory-plugin');
const bootstrapScript = resolve(pluginRoot, 'scripts/bootstrap.sh');
const autoActivateScript = resolve(pluginRoot, 'scripts/auto-activate.sh');
const observeScript = resolve(pluginRoot, 'scripts/observe-file-change.sh');

const tempDirs: string[] = [];

function makeTempDir(prefix: string): string {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  tempDirs.push(dir);
  return dir;
}

function runScript(
  scriptPath: string,
  input: Record<string, unknown>,
  env: NodeJS.ProcessEnv = {}
): Record<string, unknown> {
  const stdout = execFileSync('bash', [scriptPath], {
    input: JSON.stringify(input),
    encoding: 'utf8',
    env: {
      ...process.env,
      ...env,
    },
  });

  return JSON.parse(stdout) as Record<string, unknown>;
}

afterEach(() => {
  for (const dir of tempDirs.splice(0)) {
    execFileSync('rm', ['-rf', dir]);
  }
});

describe('pce-memory plugin scripts', () => {
  it('bootstrap configures project DB path and injects activate-first startup instructions', () => {
    const homeDir = makeTempDir('pce-plugin-home-');
    const envFile = join(homeDir, 'claude.env');
    writeFileSync(envFile, '', 'utf8');

    const result = runScript(
      bootstrapScript,
      { source: 'startup', cwd: process.cwd() },
      {
        HOME: homeDir,
        CLAUDE_ENV_FILE: envFile,
      }
    );

    const output = result['hookSpecificOutput'] as { hookEventName: string; additionalContext: string };
    expect(output.hookEventName).toBe('SessionStart');
    expect(output.additionalContext).toContain('If state is HasClaims or Ready');
    expect(output.additionalContext).toContain('allow: ["answer:task"]');
    expect(output.additionalContext).not.toContain('answer:fact');

    const envContents = readFileSync(envFile, 'utf8');
    expect(envContents).toContain('export PCE_DB=');
    expect(envContents).toContain('/.pce/projects/pce-memory/memory.db');
  });

  it('bootstrap keeps compact-mode recall focused and does not rewrite env file', () => {
    const homeDir = makeTempDir('pce-plugin-home-');
    const envFile = join(homeDir, 'claude.env');
    writeFileSync(envFile, '', 'utf8');

    const result = runScript(
      bootstrapScript,
      { source: 'compact', cwd: process.cwd() },
      {
        HOME: homeDir,
        CLAUDE_ENV_FILE: envFile,
      }
    );

    const output = result['hookSpecificOutput'] as { hookEventName: string; additionalContext: string };
    expect(output.hookEventName).toBe('SessionStart');
    expect(output.additionalContext).toContain('Context compaction occurred');
    expect(output.additionalContext).toContain('Check pce_memory_state');
    expect(output.additionalContext).toContain('allow: ["answer:task"]');
    expect(readFileSync(envFile, 'utf8')).toBe('');
  });

  it('auto-activate injects the conservative task workflow only for task-like prompts', () => {
    const taskResult = runScript(autoActivateScript, {
      userPrompt: 'Implement the auth token refresh flow',
    });
    const taskOutput = taskResult['hookSpecificOutput'] as {
      hookEventName: string;
      additionalContext: string;
    };

    expect(taskOutput.hookEventName).toBe('UserPromptSubmit');
    expect(taskOutput.additionalContext).toContain('Use pce_memory_activate as the primary recall path');
    expect(taskOutput.additionalContext).toContain('allow: ["answer:task"]');
    expect(taskOutput.additionalContext).toContain('Always write upsert text and activate queries in English');
    expect(taskOutput.additionalContext).toContain('Task detected:');
    expect(taskOutput.additionalContext).not.toContain('answer:fact');

    const nonTaskResult = runScript(autoActivateScript, {
      userPrompt: 'What does this repository do?',
    });
    const nonTaskOutput = nonTaskResult['hookSpecificOutput'] as {
      hookEventName: string;
      additionalContext: string;
    };

    expect(nonTaskOutput.additionalContext).not.toContain('Task detected:');
  });

  it('observe-file-change only emits conservative recording guidance for significant files', () => {
    const significant = runScript(observeScript, {
      tool_input: { file_path: '/tmp/src/auth/session.ts' },
    });
    const significantOutput = significant['hookSpecificOutput'] as {
      hookEventName: string;
      additionalContext: string;
    };

    expect(significantOutput.hookEventName).toBe('PostToolUse');
    expect(significantOutput.additionalContext).toContain('recording candidate only');
    expect(significantOutput.additionalContext).toContain('explicit and durable decision or constraint');

    const insignificant = runScript(observeScript, {
      tool_input: { file_path: '/tmp/src/components/Button.tsx' },
    });

    expect(insignificant).toEqual({});
  });

  it('bundled MCP config uses non-interactive npx invocation', () => {
    const configPath = resolve(pluginRoot, '.mcp.json');
    expect(existsSync(configPath)).toBe(true);

    const config = JSON.parse(readFileSync(configPath, 'utf8')) as {
      mcpServers: { 'pce-memory': { command: string; args: string[] } };
    };

    expect(config.mcpServers['pce-memory'].command).toBe('npx');
    expect(config.mcpServers['pce-memory'].args).toEqual(['-y', 'pce-memory@latest']);
  });
});

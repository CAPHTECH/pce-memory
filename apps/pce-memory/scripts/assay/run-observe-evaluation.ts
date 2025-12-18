#!/usr/bin/env npx ts-node --esm
/**
 * Observe機能評価スクリプト
 *
 * pce_memory_observe の機能テストを実行し、結果をレポートする。
 * assay-kitとは独立した評価スクリプト。
 *
 * 使用方法:
 *   npx ts-node --esm scripts/assay/run-observe-evaluation.ts
 */

import { spawn, type ChildProcess } from 'node:child_process';
import { once } from 'node:events';
import * as readline from 'node:readline';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

import { OBSERVE_TEST_CASES, type ObserveTestCase } from './observe-test-data.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, '../..');

/**
 * テスト結果
 */
interface TestResult {
  id: string;
  description: string;
  passed: boolean;
  duration: number;
  errors: string[];
  actual?: Record<string, unknown>;
}

/**
 * MCP Server プロセスを管理するクラス
 */
class McpServerRunner {
  private process: ChildProcess | null = null;
  private pendingRequests = new Map<number, (response: unknown) => void>();
  private requestId = 0;
  private rl: readline.Interface | null = null;

  async start(): Promise<void> {
    const serverPath = path.join(REPO_ROOT, 'dist/index.js');

    this.process = spawn(process.execPath, [serverPath], {
      stdio: ['pipe', 'pipe', 'inherit'],
      cwd: REPO_ROOT,
      env: { ...process.env, PCE_DB: ':memory:' },
    });

    this.rl = readline.createInterface({
      input: this.process.stdout!,
      crlfDelay: Infinity,
    });

    this.rl.on('line', (line) => {
      try {
        const msg = JSON.parse(line);
        if (msg.id && this.pendingRequests.has(msg.id)) {
          const resolve = this.pendingRequests.get(msg.id)!;
          this.pendingRequests.delete(msg.id);
          resolve(msg);
        }
      } catch {
        // JSONパースエラーは無視
      }
    });

    // Initialize
    await this.send('initialize', {
      protocolVersion: '2024-11-05',
      capabilities: {},
      clientInfo: { name: 'observe-eval', version: '1.0' },
    });
  }

  async stop(): Promise<void> {
    if (this.rl) {
      this.rl.close();
      this.rl = null;
    }
    if (this.process) {
      this.process.kill('SIGTERM');
      try {
        await Promise.race([
          once(this.process, 'exit'),
          new Promise((_, reject) => setTimeout(() => reject(new Error('timeout')), 5000)),
        ]);
      } catch {
        this.process.kill('SIGKILL');
      }
      this.process = null;
    }
  }

  async send(method: string, params: Record<string, unknown>): Promise<unknown> {
    return new Promise((resolve, reject) => {
      const id = ++this.requestId;
      this.pendingRequests.set(id, resolve);

      const request = { jsonrpc: '2.0', id, method, params };
      this.process!.stdin!.write(JSON.stringify(request) + '\n');

      setTimeout(() => {
        if (this.pendingRequests.has(id)) {
          this.pendingRequests.delete(id);
          reject(new Error(`Request ${id} timeout`));
        }
      }, 30000);
    });
  }

  async callTool(name: string, args: Record<string, unknown>): Promise<Record<string, unknown>> {
    const response = (await this.send('tools/call', { name, arguments: args })) as {
      result?: { structuredContent?: Record<string, unknown>; isError?: boolean };
    };
    return response.result?.structuredContent ?? {};
  }
}

/**
 * テストケースを実行
 */
async function runTestCase(
  runner: McpServerRunner,
  testCase: ObserveTestCase
): Promise<TestResult> {
  const startTime = Date.now();
  const errors: string[] = [];

  try {
    // observe実行
    const observeResult = await runner.callTool('pce_memory_observe', testCase.input);
    const duration = Date.now() - startTime;

    // 期待値の検証
    const expected = testCase.expected;

    // エラーケースの検証
    if (expected.is_error) {
      if (!observeResult.error) {
        errors.push(`Expected error but got success`);
      } else if (
        expected.error_code &&
        (observeResult.error as { code?: string })?.code !== expected.error_code
      ) {
        errors.push(
          `Expected error code ${expected.error_code} but got ${(observeResult.error as { code?: string })?.code}`
        );
      }
      return {
        id: testCase.id,
        description: testCase.description,
        passed: errors.length === 0,
        duration,
        errors,
        actual: observeResult,
      };
    }

    // 成功ケースの検証
    if (expected.observation_id_present !== undefined) {
      const hasId = typeof observeResult.observation_id === 'string';
      if (expected.observation_id_present !== hasId) {
        errors.push(
          `observation_id_present: expected ${expected.observation_id_present}, got ${hasId}`
        );
      }
    }

    if (expected.claim_ids_count !== undefined) {
      const count = Array.isArray(observeResult.claim_ids) ? observeResult.claim_ids.length : 0;
      if (expected.claim_ids_count !== count) {
        errors.push(`claim_ids_count: expected ${expected.claim_ids_count}, got ${count}`);
      }
    }

    if (expected.content_stored !== undefined) {
      if (expected.content_stored !== observeResult.content_stored) {
        errors.push(
          `content_stored: expected ${expected.content_stored}, got ${observeResult.content_stored}`
        );
      }
    }

    if (expected.effective_boundary_class !== undefined) {
      if (expected.effective_boundary_class !== observeResult.effective_boundary_class) {
        errors.push(
          `effective_boundary_class: expected ${expected.effective_boundary_class}, got ${observeResult.effective_boundary_class}`
        );
      }
    }

    if (expected.content_redacted !== undefined) {
      if (expected.content_redacted !== observeResult.content_redacted) {
        errors.push(
          `content_redacted: expected ${expected.content_redacted}, got ${observeResult.content_redacted}`
        );
      }
    }

    if (expected.warnings_contains) {
      const warnings = Array.isArray(observeResult.warnings) ? observeResult.warnings : [];
      for (const expectedWarning of expected.warnings_contains) {
        if (!warnings.includes(expectedWarning)) {
          errors.push(`warnings should contain "${expectedWarning}"`);
        }
      }
    }

    // claim_retrievable の検証（activateで取得できるか）
    if (
      expected.claim_retrievable &&
      Array.isArray(observeResult.claim_ids) &&
      observeResult.claim_ids.length > 0
    ) {
      const activateResult = await runner.callTool('pce_memory_activate', {
        scope: ['session'],
        allow: ['answer:task'],
        include_meta: true,
      });

      const claims = Array.isArray(activateResult.claims) ? activateResult.claims : [];
      const claimId = observeResult.claim_ids[0];
      const found = claims.some(
        (c: unknown) =>
          c &&
          typeof c === 'object' &&
          'claim' in c &&
          (c as { claim?: { id?: string } }).claim?.id === claimId
      );

      if (!found) {
        errors.push(`claim_retrievable: claim ${claimId} not found in activate results`);
      }

      // claim_has_evidence の検証
      if (expected.claim_has_evidence && found) {
        const matchedClaim = claims.find(
          (c: unknown) =>
            c &&
            typeof c === 'object' &&
            'claim' in c &&
            (c as { claim?: { id?: string } }).claim?.id === claimId
        ) as { evidences?: Array<{ source_type?: string; source_id?: string }> } | undefined;

        const evidences = matchedClaim?.evidences ?? [];
        const hasObservationEvidence = evidences.some(
          (e) => e.source_type === 'observation' && e.source_id === observeResult.observation_id
        );

        if (!hasObservationEvidence) {
          errors.push(`claim_has_evidence: observation evidence not found for claim ${claimId}`);
        }
      }
    }

    return {
      id: testCase.id,
      description: testCase.description,
      passed: errors.length === 0,
      duration,
      errors,
      actual: observeResult,
    };
  } catch (e) {
    return {
      id: testCase.id,
      description: testCase.description,
      passed: false,
      duration: Date.now() - startTime,
      errors: [e instanceof Error ? e.message : String(e)],
    };
  }
}

/**
 * メイン関数
 */
async function main() {
  console.log('🧪 PCE-Memory Observe Evaluation');
  console.log('='.repeat(50));
  console.log(`📋 Test cases: ${OBSERVE_TEST_CASES.length}`);
  console.log('');

  const runner = new McpServerRunner();

  try {
    console.log('🚀 Starting MCP server...');
    await runner.start();

    // ポリシー適用
    console.log('📋 Applying policy...');
    await runner.callTool('pce_memory_policy_apply', {});

    console.log('✅ Server ready\n');

    // テスト実行
    const results: TestResult[] = [];
    let passed = 0;
    let failed = 0;

    for (const testCase of OBSERVE_TEST_CASES) {
      process.stdout.write(`  ${testCase.id}: ${testCase.description}... `);

      const result = await runTestCase(runner, testCase);
      results.push(result);

      if (result.passed) {
        passed++;
        console.log(`✅ (${result.duration}ms)`);
      } else {
        failed++;
        console.log(`❌ (${result.duration}ms)`);
        for (const error of result.errors) {
          console.log(`    └─ ${error}`);
        }
      }
    }

    // サマリー
    console.log('');
    console.log('='.repeat(50));
    console.log('📊 Results Summary');
    console.log(`  ✅ Passed: ${passed}`);
    console.log(`  ❌ Failed: ${failed}`);
    console.log(`  📈 Pass rate: ${((passed / (passed + failed)) * 100).toFixed(1)}%`);

    // 失敗したテストの詳細
    if (failed > 0) {
      console.log('');
      console.log('❌ Failed Tests:');
      for (const result of results.filter((r) => !r.passed)) {
        console.log(`  - ${result.id}: ${result.description}`);
        for (const error of result.errors) {
          console.log(`      ${error}`);
        }
      }
    }

    process.exit(failed > 0 ? 1 : 0);
  } finally {
    await runner.stop();
  }
}

main().catch((e) => {
  console.error('Fatal error:', e);
  process.exit(1);
});

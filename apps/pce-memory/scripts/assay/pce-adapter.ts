/**
 * PCE-Memory Search Adapter for assay-kit
 *
 * assay-kitのSearchAdapterインターフェースを実装し、
 * pce-memory daemonと通信してactivate検索を評価する。
 */

import { spawn, type ChildProcess } from 'node:child_process';
import { once } from 'node:events';
import * as net from 'node:net';
import * as readline from 'node:readline';
import * as path from 'node:path';
import * as fs from 'node:fs/promises';
import * as os from 'node:os';

import type {
  SearchAdapter,
  SearchAdapterContext,
  Metrics,
  Query,
  Dataset,
} from '../../external/assay-kit/packages/assay-kit/src/index.ts';
import { evaluateRetrieval } from '../../external/assay-kit/packages/assay-kit/src/index.ts';

import { TEST_CLAIMS, TEST_POLICY } from './test-data.ts';

const TIMESTAMP_INTERVAL_MS = 10;

/**
 * JSON-RPCリクエスト型
 */
interface JsonRpcRequest {
  jsonrpc: '2.0';
  id: string | number;
  method: string;
  params?: Record<string, unknown>;
}

/**
 * JSON-RPCレスポンス型
 */
interface JsonRpcResponse {
  jsonrpc: '2.0';
  id: string | number | null;
  result?: unknown;
  error?: {
    code: number;
    message: string;
  };
}

/**
 * pce-memory用クエリメタデータ
 */
interface PceQueryMetadata extends Record<string, unknown> {
  category?: string;
  intent?: string;
  expected?: Array<string | { path: string; relevance: number }>;
}

type PceQuery = Query<Record<string, unknown>, PceQueryMetadata>;

/**
 * PCE-Memory Search Adapter
 */
export class PceMemorySearchAdapter implements SearchAdapter<PceQuery, Metrics> {
  private daemonProcess: ChildProcess | null = null;
  private socketPath: string;
  private readonly databasePath: string;
  private readonly repoRoot: string;
  private daemonLogs = '';
  private requestId = 0;
  // テストデータのID → 生成されたclaim IDのマッピング
  private testIdToClaimId: Map<string, string> = new Map();

  constructor(databasePath: string, repoRoot: string) {
    this.databasePath = databasePath;
    this.repoRoot = repoRoot;
    // ソケットパスはDBパスに.sockを追加（daemonと同じロジック）
    this.socketPath = `${databasePath}.sock`;
  }

  /**
   * ウォームアップ: daemon起動、ポリシー適用、テストデータ投入
   */
  async warmup(dataset: Dataset<PceQuery>): Promise<void> {
    console.log('🚀 Starting PCE-Memory daemon...');

    // DBディレクトリを作成
    const dbDir = path.dirname(this.databasePath);
    await fs.mkdir(dbDir, { recursive: true });

    // 既存のソケットファイルを削除
    try {
      await fs.unlink(this.socketPath);
    } catch {
      // 存在しない場合は無視
    }

    // daemonを起動
    const daemonPath = path.join(this.repoRoot, 'dist/daemon/daemon.js');
    this.daemonProcess = spawn(
      process.execPath,
      [daemonPath, '--db', this.databasePath],
      {
        stdio: ['ignore', 'pipe', 'pipe'],
        cwd: this.repoRoot,
        env: process.env,
      }
    );

    this.daemonProcess.stdout?.on('data', (data) => {
      this.daemonLogs += data.toString();
    });

    this.daemonProcess.stderr?.on('data', (data) => {
      this.daemonLogs += data.toString();
    });

    this.daemonProcess.on('error', (error) => {
      console.error('PCE-Memory daemon process error:', error);
    });

    // daemon準備完了を待機
    await this.waitForReady();
    console.log('✅ PCE-Memory daemon ready');

    // ポリシー適用
    console.log('📋 Applying policy...');
    await this.callTool('pce.memory.policy.apply', {
      policy: TEST_POLICY,
    });

    // テストデータ投入
    console.log(`📝 Upserting ${TEST_CLAIMS.length} test claims...`);
    for (const claim of TEST_CLAIMS) {
      const result = await this.callTool('pce.memory.upsert', claim);
      // テストIDと生成されたclaim IDのマッピングを保存
      if (result && typeof result === 'object' && 'id' in result) {
        const generatedId = (result as { id: string }).id;
        this.testIdToClaimId.set(claim.id, generatedId);
      }
    }

    console.log('✅ Warmup completed');
  }

  /**
   * クエリ実行: pce.memory.activateを呼び出しメトリクスを計算
   */
  async execute(query: PceQuery, ctx: SearchAdapterContext): Promise<Metrics> {
    const startTime = Date.now();

    if (ctx.signal.aborted) {
      throw new Error(`Query ${query.id} was cancelled`);
    }

    try {
      const result = await this.callTool('pce.memory.activate', {
        q: query.text,
        scope: ['session', 'project', 'principle'],
        allow: ['answer:task'],
        top_k: ctx.options.k ?? 10,
      });

      const latencyMs = Date.now() - startTime;

      // 結果からclaimsを抽出
      const claims = this.extractClaims(result);
      const retrievedIds = claims.map((c) => c.id);
      const expectedIds = this.getExpectedIds(query);
      const k = ctx.options.k ?? 10;

      // 関連度マップを構築
      const { relevanceGrades, relevantIds } = this.buildRelevanceGrades(query);

      // メトリクス計算
      const retrievalMetrics = evaluateRetrieval({
        items: retrievedIds.map((id, i) => ({
          id,
          timestampMs: startTime + i * TIMESTAMP_INTERVAL_MS,
        })),
        relevant: relevanceGrades.size > 0 ? relevantIds : expectedIds,
        k,
        startTimestampMs: startTime,
        ...(relevanceGrades.size > 0 && { relevanceGrades }),
      });

      return {
        latencyMs,
        precision: retrievalMetrics.precisionAtK,
        recall: retrievalMetrics.recallAtK,
        extras: {
          resultCount: retrievedIds.length,
          k,
          mrr: retrievalMetrics.mrr,
          map: retrievalMetrics.map,
          hitsAtK: retrievalMetrics.hitsAtK,
          f1: retrievalMetrics.f1,
          ttfu: retrievalMetrics.timeToFirstUseful,
          ndcg: retrievalMetrics.ndcg ?? 0,
        },
      };
    } catch (error) {
      throw new Error(
        `PCE-Memory query failed for ${query.id}: ${error instanceof Error ? error.message : String(error)}`
      );
    }
  }

  /**
   * 停止: daemonプロセスを終了
   */
  async stop(reason?: string): Promise<void> {
    console.log(`🛑 Stopping PCE-Memory daemon${reason ? `: ${reason}` : ''}...`);

    const proc = this.daemonProcess;
    if (!proc) {
      console.log('✅ PCE-Memory daemon already stopped');
      return;
    }

    this.daemonProcess = null;
    proc.kill('SIGTERM');

    try {
      await Promise.race([
        once(proc, 'exit'),
        new Promise((_, reject) => setTimeout(() => reject(new Error('timeout')), 5000)),
      ]);
    } catch {
      proc.kill('SIGKILL');
      try {
        await once(proc, 'exit');
      } catch {
        // ignore
      }
    } finally {
      proc.removeAllListeners();
    }

    // ソケットファイルを削除
    try {
      await fs.unlink(this.socketPath);
    } catch {
      // ignore
    }

    console.log('✅ PCE-Memory daemon stopped');
  }

  /**
   * daemon準備完了を待機
   */
  private async waitForReady(): Promise<void> {
    const maxAttempts = 30;
    const delayMs = 1000;

    for (let attempt = 0; attempt < maxAttempts; attempt++) {
      try {
        await this.sendJsonRpc('ping', {});
        return;
      } catch {
        // まだ準備できていない
      }
      await new Promise((resolve) => setTimeout(resolve, delayMs));
    }

    throw new Error(
      `PCE-Memory daemon failed to start within ${maxAttempts} seconds.\nDaemon logs:\n${this.daemonLogs}`
    );
  }

  /**
   * MCPツールを呼び出す
   */
  private async callTool(name: string, args: Record<string, unknown>): Promise<unknown> {
    const response = await this.sendJsonRpc('tools/call', {
      name,
      arguments: args,
    });

    // MCPレスポンスからcontentを抽出
    if (response && typeof response === 'object' && 'content' in response) {
      const content = (response as { content: Array<{ type: string; text: string }> }).content;
      if (Array.isArray(content) && content.length > 0 && content[0].type === 'text') {
        return JSON.parse(content[0].text);
      }
    }

    return response;
  }

  /**
   * Unix socket経由でJSON-RPCリクエストを送信
   */
  private sendJsonRpc(method: string, params: Record<string, unknown>): Promise<unknown> {
    return new Promise((resolve, reject) => {
      let resolved = false;
      const id = ++this.requestId;

      const request: JsonRpcRequest = {
        jsonrpc: '2.0',
        id,
        method,
        params,
      };

      const cleanup = (socket: net.Socket, rl?: readline.Interface) => {
        rl?.close();
        socket.destroy();
      };

      const handleError = (err: Error, socket: net.Socket, rl?: readline.Interface) => {
        if (!resolved) {
          resolved = true;
          cleanup(socket, rl);
          reject(err);
        }
      };

      const socket = net.createConnection(this.socketPath);

      // エラーハンドラは最初に設定
      socket.on('error', (err) => {
        handleError(err, socket);
      });

      socket.on('connect', () => {
        const rl = readline.createInterface({
          input: socket,
          crlfDelay: Infinity,
        });

        // readlineのエラーハンドラも設定
        rl.on('error', (err) => {
          handleError(err, socket, rl);
        });

        rl.on('line', (line) => {
          if (resolved) return;
          try {
            const response = JSON.parse(line) as JsonRpcResponse;
            if (response.id === id) {
              resolved = true;
              cleanup(socket, rl);
              if (response.error) {
                reject(new Error(response.error.message));
              } else {
                resolve(response.result);
              }
            }
          } catch {
            // パースエラーは無視
          }
        });

        socket.write(JSON.stringify(request) + '\n');
      });

      // タイムアウト
      setTimeout(() => {
        if (!resolved) {
          resolved = true;
          socket.destroy();
          reject(new Error('Request timeout'));
        }
      }, 30000);
    });
  }

  /**
   * activate結果からclaimsを抽出
   *
   * activateの結果は { claims: [{ claim: {...}, score, evidences }, ...] } 形式
   */
  private extractClaims(result: unknown): Array<{ id: string }> {
    if (!result || typeof result !== 'object') {
      return [];
    }

    // activateの結果はclaims配列を含む（各要素は { claim, score, evidences } 形式）
    if ('claims' in result && Array.isArray((result as { claims?: unknown }).claims)) {
      const claims = (result as { claims: Array<{ claim?: { id: string } }> }).claims;
      return claims
        .filter((item) => item.claim && typeof item.claim.id === 'string')
        .map((item) => ({ id: item.claim!.id }));
    }

    return [];
  }

  /**
   * クエリから期待されるIDリストを取得
   * テストIDから生成されたclaim IDにマッピングする
   */
  private getExpectedIds(query: PceQuery): string[] {
    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) {
      return [];
    }

    return expected.map((item) => {
      let testId = '';
      if (typeof item === 'string') {
        testId = item;
      } else if (typeof item === 'object' && 'path' in item) {
        testId = item.path;
      }
      // テストIDを生成されたclaim IDに変換
      return this.testIdToClaimId.get(testId) ?? testId;
    }).filter(Boolean);
  }

  /**
   * 関連度マップを構築
   * テストIDから生成されたclaim IDにマッピングする
   */
  private buildRelevanceGrades(query: PceQuery): {
    relevanceGrades: Map<string, number>;
    relevantIds: string[];
  } {
    const relevanceGrades = new Map<string, number>();
    const relevantIds: string[] = [];

    const expected = query.metadata?.expected;
    if (!Array.isArray(expected)) {
      return { relevanceGrades, relevantIds };
    }

    for (const item of expected) {
      if (typeof item === 'object' && 'path' in item && 'relevance' in item) {
        const testId = item.path;
        const relevance = item.relevance;
        if (typeof testId === 'string' && typeof relevance === 'number') {
          // テストIDを生成されたclaim IDに変換
          const claimId = this.testIdToClaimId.get(testId) ?? testId;
          relevanceGrades.set(claimId, relevance);
          if (relevance > 0) {
            relevantIds.push(claimId);
          }
        }
      } else if (typeof item === 'string') {
        const claimId = this.testIdToClaimId.get(item) ?? item;
        relevanceGrades.set(claimId, 1);
        relevantIds.push(claimId);
      }
    }

    return { relevanceGrades, relevantIds };
  }
}

/**
 * アダプターファクトリ関数
 */
export function createPceMemoryAdapter(
  databasePath: string,
  repoRoot: string
): PceMemorySearchAdapter {
  return new PceMemorySearchAdapter(databasePath, repoRoot);
}

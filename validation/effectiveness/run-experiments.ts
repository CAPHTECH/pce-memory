#!/usr/bin/env node

import { spawn, type ChildProcessWithoutNullStreams } from 'node:child_process';
import { createHash } from 'node:crypto';
import { promises as fs } from 'node:fs';
import { tmpdir } from 'node:os';
import path from 'node:path';
import readline from 'node:readline';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const REPO_ROOT = path.resolve(__dirname, '../..');
const RESULTS_DIR = path.join(REPO_ROOT, 'validation/effectiveness/results');
const MCP_SERVER_PATH = path.join(REPO_ROOT, 'apps/pce-memory/dist/index.js');
const TARGET_FILE_PATH = path.join(REPO_ROOT, 'apps/pce-memory/src/store/hybridSearch.ts');
const TARGET_FILE_LABEL = 'apps/pce-memory/src/store/hybridSearch.ts';
const OLLAMA_CHAT_URL =
  process.env.OLLAMA_API_URL ?? 'http://localhost:11434/v1/chat/completions';
const OLLAMA_MODELS_URL =
  process.env.OLLAMA_MODELS_URL ?? 'http://localhost:11434/v1/models';
const OLLAMA_MODEL = process.env.OLLAMA_MODEL ?? 'qwen3.5:122b-a10b';
const MAX_TOKENS = parsePositiveInt(process.env.OLLAMA_MAX_TOKENS) ?? 1500;
const JSON_RETRY_MAX_TOKENS =
  parsePositiveInt(process.env.OLLAMA_JSON_RETRY_MAX_TOKENS) ?? Math.max(MAX_TOKENS * 2, 3000);
const REASONING_EFFORT = process.env.OLLAMA_REASONING_EFFORT ?? 'none';
const CHAT_TEMPERATURE = 0;
const CHAT_TIMEOUT_MS = 180_000;
const RPC_TIMEOUT_MS = 60_000;
const JSON_RPC_VERSION = '2.0';
const MCP_PROTOCOL_VERSION = '2024-11-05';

type ChatRole = 'system' | 'user' | 'assistant';

interface ChatMessage {
  role: ChatRole;
  content: string;
}

interface ChatCompletionChoice {
  finish_reason?: string | null;
  message?: {
    role?: string;
    content?: string | null;
    reasoning?: string | null;
  };
}

interface ChatCompletionResponse {
  id?: string;
  choices?: ChatCompletionChoice[];
  usage?: Record<string, unknown>;
}

interface OllamaModelDescriptor {
  id?: string;
}

interface OllamaModelsResponse {
  data?: OllamaModelDescriptor[];
}

interface JsonRpcRequest {
  jsonrpc: '2.0';
  id: number;
  method: string;
  params?: Record<string, unknown>;
}

interface JsonRpcResponse {
  jsonrpc: '2.0';
  id?: number | null;
  result?: unknown;
  error?: {
    code?: number;
    message?: string;
  };
}

interface Improvement {
  slug: string;
  title: string;
  why: string;
  evidence: string[];
}

interface ImprovementPayload {
  improvements: Improvement[];
}

interface ImprovementRecallItem {
  slug: string;
  explanation: string;
  evidence: string[];
}

interface ImprovementRecallPayload {
  status: 'ok' | 'no_context';
  improvements: ImprovementRecallItem[];
}

interface DecisionSeed {
  id: string;
  text: string;
}

interface DecisionRecallItem {
  id: string;
  summary: string;
  params: string[];
}

interface DecisionRecallPayload {
  status: 'ok' | 'no_context';
  decisions: DecisionRecallItem[];
}

interface AnchorScore {
  matched: string[];
  missing: string[];
  total: number;
}

interface CompletionMeta {
  mode: 'content' | 'empty';
  has_reasoning: boolean;
  finish_reason?: string;
  invalid_reasons: string[];
}

interface ContinuityScore {
  slug_recall: AnchorScore;
  evidence_recall: AnchorScore;
  generic_markers: string[];
  invalid_reasons: string[];
  verdict: 'specific_recall' | 'partial_recall' | 'generic_or_no_context' | 'invalid_response';
}

interface DecisionScore {
  decision_id_recall: AnchorScore;
  detail_recall: AnchorScore;
  generic_markers: string[];
  invalid_reasons: string[];
  verdict: 'specific_recall' | 'partial_recall' | 'generic_or_no_context' | 'invalid_response';
}

interface ArmBase {
  condition: 'with_memory' | 'without_memory';
  setup_error?: string;
}

interface TaskContinuityArm extends ArmBase {
  phase_a: {
    prompt: string;
    response: string;
    parsed?: ImprovementPayload;
    meta: CompletionMeta;
  };
  phase_b: {
    question: string;
    response: string;
    parsed?: ImprovementRecallPayload;
    meta: CompletionMeta;
  };
  tool_transcript?: string;
  memory_actions?: {
    observe: unknown;
    upserts: unknown[];
    activate: unknown;
  };
  score: ContinuityScore;
}

interface DesignRecallArm extends ArmBase {
  seeded_decisions?: DecisionSeed[];
  question: string;
  response: string;
  parsed?: DecisionRecallPayload;
  meta: CompletionMeta;
  tool_transcript?: string;
  memory_actions?: {
    upserts: unknown[];
    activate: unknown;
  };
  score: DecisionScore;
}

interface ExperimentResults {
  generated_at: string;
  configuration: {
    ollama_chat_url: string;
    ollama_models_url: string;
    model: string;
    max_tokens: number;
    json_retry_max_tokens: number;
    reasoning_effort: string;
    temperature: number;
    target_file: string;
    mcp_server: string;
  };
  preflight: {
    available_models: string[];
  };
  experiments: {
    task_continuity: {
      with_memory: TaskContinuityArm;
      without_memory: TaskContinuityArm;
    };
    design_decision_recall: {
      with_memory: DesignRecallArm;
      without_memory: DesignRecallArm;
    };
  };
}

class OllamaClient {
  async listModels(): Promise<string[]> {
    const response = await fetchWithTimeout(OLLAMA_MODELS_URL, {
      method: 'GET',
      headers: { Accept: 'application/json' },
    });
    const payload = (await response.json()) as OllamaModelsResponse;
    return (payload.data ?? [])
      .map((entry) => entry.id)
      .filter((id): id is string => typeof id === 'string' && id.length > 0);
  }

  async chat(
    messages: ChatMessage[],
    options: {
      jsonMode?: boolean;
      forceJsonSchema?: boolean;
      maxTokensOverride?: number;
    } = {}
  ): Promise<{ text: string; raw: ChatCompletionResponse; meta: CompletionMeta }> {
    const initialPayload = await this.requestChat(messages, options);
    const initialText = extractCompletionText(initialPayload);
    const initialMeta = buildCompletionMeta(
      initialPayload,
      { jsonMode: options.jsonMode === true },
      initialText
    );

    if (
      options.jsonMode === true &&
      initialText.length === 0 &&
      initialMeta.finish_reason === 'length' &&
      (options.maxTokensOverride ?? MAX_TOKENS) < JSON_RETRY_MAX_TOKENS
    ) {
      const retryPayload = await this.requestChat(
        [
          systemMessage(
            'The previous attempt exhausted tokens before the final JSON. Return the final JSON object immediately with no extra analysis.'
          ),
          ...messages,
        ],
        {
          ...options,
          maxTokensOverride: JSON_RETRY_MAX_TOKENS,
        }
      );
      const retryText = extractCompletionText(retryPayload);
      return {
        text: retryText,
        raw: retryPayload,
        meta: buildCompletionMeta(retryPayload, { jsonMode: true }, retryText),
      };
    }

    return {
      text: initialText,
      raw: initialPayload,
      meta: initialMeta,
    };
  }

  async chatForImprovements(
    messages: ChatMessage[]
  ): Promise<{ text: string; parsed: ImprovementPayload; raw: ChatCompletionResponse; meta: CompletionMeta }> {
    const completion = await this.chat(messages, {
      jsonMode: true,
      forceJsonSchema: true,
    });
    if (completion.text.length === 0) {
      throw new Error(`Ollama returned an empty improvement response: ${JSON.stringify(completion.raw)}`);
    }
    const parsed = parseImprovementPayload(completion.text);
    return { ...completion, parsed };
  }

  private async requestChat(
    messages: ChatMessage[],
    options: {
      jsonMode?: boolean;
      forceJsonSchema?: boolean;
      maxTokensOverride?: number;
    }
  ): Promise<ChatCompletionResponse> {
    const response = await fetchWithTimeout(OLLAMA_CHAT_URL, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json',
        Accept: 'application/json',
      },
      body: JSON.stringify({
      model: OLLAMA_MODEL,
      max_tokens: options.maxTokensOverride ?? MAX_TOKENS,
      reasoning_effort: REASONING_EFFORT,
      temperature: CHAT_TEMPERATURE,
        stream: false,
        messages,
        ...(options.jsonMode
          ? {
              response_format: options.forceJsonSchema
                ? { type: 'json_object' }
                : { type: 'text' },
            }
          : {}),
      }),
    });

    return (await response.json()) as ChatCompletionResponse;
  }
}

class McpMemoryClient {
  private process: ChildProcessWithoutNullStreams | null = null;
  private requestId = 0;
  private readonly pending = new Map<
    number,
    {
      resolve: (value: JsonRpcResponse | null) => void;
      reject: (reason?: unknown) => void;
      timeout: NodeJS.Timeout;
    }
  >();
  private stdoutReader: readline.Interface | null = null;
  private stderrBuffer = '';

  constructor(private readonly dbPath: string) {}

  get stderrLogs(): string {
    return this.stderrBuffer.trim();
  }

  async start(): Promise<void> {
    this.process = spawn(process.execPath, [MCP_SERVER_PATH], {
      cwd: REPO_ROOT,
      env: {
        ...process.env,
        PCE_DB: this.dbPath,
      },
      stdio: ['pipe', 'pipe', 'pipe'],
    });

    this.process.on('error', (error) => {
      this.rejectAllPending(error);
    });
    this.process.on('exit', (code, signal) => {
      if (code === 0 || signal === 'SIGTERM') {
        this.rejectAllPending(new Error('MCP server exited before pending requests completed.'));
        return;
      }
      this.rejectAllPending(
        new Error(`MCP server exited unexpectedly with code=${code ?? 'null'} signal=${signal ?? 'null'}`)
      );
    });

    this.stdoutReader = readline.createInterface({
      input: this.process.stdout,
      crlfDelay: Infinity,
    });
    this.stdoutReader.on('line', (line) => {
      const trimmed = line.trim();
      if (!trimmed) {
        return;
      }
      let payload: JsonRpcResponse | null = null;
      try {
        payload = JSON.parse(trimmed) as JsonRpcResponse;
      } catch {
        return;
      }
      if (payload?.id === undefined || payload.id === null) {
        return;
      }
      const pending = this.pending.get(payload.id);
      if (!pending) {
        return;
      }
      clearTimeout(pending.timeout);
      this.pending.delete(payload.id);
      pending.resolve(payload);
    });

    this.process.stderr.on('data', (chunk) => {
      this.stderrBuffer += chunk.toString();
    });

    await this.send('initialize', {
      protocolVersion: MCP_PROTOCOL_VERSION,
      capabilities: {},
      clientInfo: {
        name: 'validation-effectiveness-harness',
        version: '1.0.0',
      },
    });
    await this.notify('notifications/initialized');

    const state = (await this.callTool('pce_memory_state', {})) as { state?: string };
    if (state.state === 'Uninitialized') {
      await this.callTool('pce_memory_policy_apply', {});
    }
  }

  async stop(): Promise<void> {
    for (const pending of this.pending.values()) {
      clearTimeout(pending.timeout);
      pending.reject(new Error('MCP client stopped.'));
    }
    this.pending.clear();

    this.stdoutReader?.close();
    this.stdoutReader = null;

    if (!this.process) {
      return;
    }

    const proc = this.process;
    this.process = null;

    proc.stdin.end();
    const exited = await new Promise<boolean>((resolve) => {
      const timer = setTimeout(() => resolve(false), 3_000);
      proc.once('exit', () => {
        clearTimeout(timer);
        resolve(true);
      });
    });

    if (!exited) {
      proc.kill('SIGTERM');
      const terminated = await new Promise<boolean>((resolve) => {
        const timer = setTimeout(() => resolve(false), 2_000);
        proc.once('exit', () => {
          clearTimeout(timer);
          resolve(true);
        });
      });
      if (!terminated) {
        proc.kill('SIGKILL');
      }
    }
  }

  async callTool(name: string, args: Record<string, unknown>): Promise<unknown> {
    const response = await this.send('tools/call', {
      name,
      arguments: args,
    });

    if (response?.error) {
      throw new Error(
        `Tool ${name} failed: ${response.error.message ?? JSON.stringify(response.error)}`
      );
    }

    const result = response?.result as
      | {
          isError?: boolean;
          structuredContent?: unknown;
          content?: Array<{ type?: string; text?: string }>;
        }
      | undefined;

    if (result?.isError) {
      throw new Error(`Tool ${name} returned an error payload: ${JSON.stringify(result)}`);
    }

    if (result?.structuredContent !== undefined) {
      return result.structuredContent;
    }

    const fallbackText = result?.content
      ?.map((entry) => entry.text)
      .filter((value): value is string => typeof value === 'string')
      .join('\n');

    if (fallbackText && fallbackText.trim().length > 0) {
      try {
        return JSON.parse(fallbackText);
      } catch {
        return { text: fallbackText };
      }
    }

    return {};
  }

  private async send(
    method: string,
    params?: Record<string, unknown>,
    expectResponse = true
  ): Promise<JsonRpcResponse | null> {
    if (!this.process) {
      throw new Error('MCP server is not running.');
    }

    const id = ++this.requestId;
    const payload: JsonRpcRequest = {
      jsonrpc: JSON_RPC_VERSION,
      id,
      method,
      ...(params ? { params } : {}),
    };

    const line = JSON.stringify(payload) + '\n';
    if (!expectResponse) {
      this.process.stdin.write(line);
      return null;
    }

    return await new Promise<JsonRpcResponse | null>((resolve, reject) => {
      const timeout = setTimeout(() => {
        this.pending.delete(id);
        reject(new Error(`Timed out waiting for JSON-RPC response to ${method}.`));
      }, RPC_TIMEOUT_MS);

      this.pending.set(id, { resolve, reject, timeout });
      this.process!.stdin.write(line);
    });
  }

  private async notify(method: string, params?: Record<string, unknown>): Promise<void> {
    await this.send(method, params, false);
  }

  private rejectAllPending(reason: unknown): void {
    for (const [id, pending] of this.pending.entries()) {
      clearTimeout(pending.timeout);
      pending.reject(reason);
      this.pending.delete(id);
    }
  }
}

async function main(): Promise<void> {
  await fs.mkdir(RESULTS_DIR, { recursive: true });

  const client = new OllamaClient();
  const availableModels = await client.listModels();
  if (!availableModels.includes(OLLAMA_MODEL)) {
    throw new Error(
      `Model ${OLLAMA_MODEL} is not available from ${OLLAMA_MODELS_URL}. Available models: ${availableModels.join(', ')}`
    );
  }

  const sourceCode = await fs.readFile(TARGET_FILE_PATH, 'utf8');

  const taskContinuityWithMemory = await runTaskContinuityWithMemory(client, sourceCode);
  const taskContinuityWithoutMemory = await runTaskContinuityWithoutMemory(client, sourceCode);
  const designRecallWithMemory = await runDesignDecisionRecallWithMemory(client);
  const designRecallWithoutMemory = await runDesignDecisionRecallWithoutMemory(client);

  const results: ExperimentResults = {
    generated_at: new Date().toISOString(),
    configuration: {
      ollama_chat_url: OLLAMA_CHAT_URL,
      ollama_models_url: OLLAMA_MODELS_URL,
      model: OLLAMA_MODEL,
      max_tokens: MAX_TOKENS,
      json_retry_max_tokens: JSON_RETRY_MAX_TOKENS,
      reasoning_effort: REASONING_EFFORT,
      temperature: CHAT_TEMPERATURE,
      target_file: TARGET_FILE_LABEL,
      mcp_server: path.relative(REPO_ROOT, MCP_SERVER_PATH),
    },
    preflight: {
      available_models: availableModels,
    },
    experiments: {
      task_continuity: {
        with_memory: taskContinuityWithMemory,
        without_memory: taskContinuityWithoutMemory,
      },
      design_decision_recall: {
        with_memory: designRecallWithMemory,
        without_memory: designRecallWithoutMemory,
      },
    },
  };

  const jsonPath = path.join(RESULTS_DIR, 'experiment-results.json');
  const reportPath = path.join(RESULTS_DIR, 'report.md');

  await fs.writeFile(jsonPath, JSON.stringify(results, null, 2) + '\n', 'utf8');
  await fs.writeFile(reportPath, buildReport(results), 'utf8');

  console.log(`Wrote ${path.relative(REPO_ROOT, jsonPath)}`);
  console.log(`Wrote ${path.relative(REPO_ROOT, reportPath)}`);
  console.log('');
  console.log(
    `Experiment 1: with-memory slug recall ${results.experiments.task_continuity.with_memory.score.slug_recall.matched.length}/${results.experiments.task_continuity.with_memory.score.slug_recall.total}, without-memory ${results.experiments.task_continuity.without_memory.score.slug_recall.matched.length}/${results.experiments.task_continuity.without_memory.score.slug_recall.total}`
  );
  console.log(
    `Experiment 2: with-memory decision recall ${results.experiments.design_decision_recall.with_memory.score.decision_id_recall.matched.length}/${results.experiments.design_decision_recall.with_memory.score.decision_id_recall.total}, without-memory ${results.experiments.design_decision_recall.without_memory.score.decision_id_recall.matched.length}/${results.experiments.design_decision_recall.without_memory.score.decision_id_recall.total}`
  );
}

async function runTaskContinuityWithMemory(
  client: OllamaClient,
  sourceCode: string
): Promise<TaskContinuityArm> {
  const dbPath = await createTempDbPath('task-continuity-with-memory');
  const memory = new McpMemoryClient(dbPath);
  await memory.start();

  try {
    const phaseAPrompt = buildPhaseAAnalyzePrompt(sourceCode);
    const phaseA = await client.chatForImprovements([
      systemMessage(
        'You are performing a focused code-review pass. Return JSON only and keep all findings grounded in the supplied file.'
      ),
      userMessage(phaseAPrompt),
    ]);

    const observeInput = {
      source_type: 'chat',
      boundary_class: 'internal',
      content: [
        `Experiment 1 Phase A findings for ${TARGET_FILE_LABEL}.`,
        JSON.stringify(phaseA.parsed, null, 2),
      ].join('\n'),
      tags: ['validation', 'effectiveness', 'task-continuity'],
    };
    const observeResult = await memory.callTool('pce_memory_observe', observeInput);

    const upserts: unknown[] = [];
    for (const improvement of phaseA.parsed.improvements) {
      const text = formatImprovementClaim(improvement);
      const payload = {
        text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        content_hash: sha256(text),
        provenance: {
          at: new Date().toISOString(),
          actor: 'validation-harness',
          note: 'validation/effectiveness experiment1 task continuity',
        },
      };
      const upsertResult = await memory.callTool('pce_memory_upsert', payload);
      upserts.push(upsertResult);
    }

    const phaseBQuestion =
      'What improvements were identified in the previous session for hybridSearch.ts?';
    const activateArgs = {
      intent: 'resume_task',
      q: 'hybridSearch.ts previous session improvements',
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 10,
      include_meta: true,
      kind_filter: ['fact'],
      memory_type_filter: ['knowledge'],
    };
    const activateRaw = await memory.callTool('pce_memory_activate', activateArgs);
    const activateSummary = summarizeActivateResult(activateRaw);
    const toolTranscript = buildToolTranscript('pce_memory_activate', activateArgs, activateSummary);

    const phaseB = await client.chat([
      systemMessage(
        'You are answering a task-resume question. Use the provided simulated MCP tool result as authoritative prior-session memory, and do not invent details that are absent from it.'
      ),
      systemMessage(buildTaskContinuityRecallInstructions()),
      systemMessage(toolTranscript),
      userMessage(phaseBQuestion),
    ], {
      jsonMode: true,
      forceJsonSchema: true,
    });
    const phaseBParsed = tryParseImprovementRecallPayload(phaseB.text);
    const phaseBMeta = mergeMetaInvalidReasons(phaseB.meta, phaseBParsed.invalid_reasons);

    return {
      condition: 'with_memory',
      phase_a: {
        prompt: phaseAPrompt,
        response: phaseA.text,
        parsed: phaseA.parsed,
        meta: phaseA.meta,
      },
      phase_b: {
        question: phaseBQuestion,
        response: phaseB.text,
        parsed: phaseBParsed.value,
        meta: phaseBMeta,
      },
      tool_transcript: toolTranscript,
      memory_actions: {
        observe: observeResult,
        upserts,
        activate: activateRaw,
      },
      score: scoreTaskContinuity(
        phaseA.parsed.improvements,
        phaseBParsed.value,
        phaseB.text,
        phaseBMeta
      ),
    };
  } finally {
    await memory.stop();
  }
}

async function runTaskContinuityWithoutMemory(
  client: OllamaClient,
  sourceCode: string
): Promise<TaskContinuityArm> {
  const phaseAPrompt = buildPhaseAAnalyzePrompt(sourceCode);
  const phaseA = await client.chatForImprovements([
    systemMessage(
      'You are performing a focused code-review pass. Return JSON only and keep all findings grounded in the supplied file.'
    ),
    userMessage(phaseAPrompt),
  ]);

  const phaseBQuestion =
    'What improvements were identified in the previous session for hybridSearch.ts?';
  const phaseB = await client.chat([
    systemMessage(
      'You are answering from the current conversation only. If previous-session context is missing, avoid pretending that you have it.'
    ),
    systemMessage(buildTaskContinuityRecallInstructions()),
    userMessage(phaseBQuestion),
  ], {
    jsonMode: true,
    forceJsonSchema: true,
  });
  const phaseBParsed = tryParseImprovementRecallPayload(phaseB.text);
  const phaseBMeta = mergeMetaInvalidReasons(phaseB.meta, phaseBParsed.invalid_reasons);

  return {
    condition: 'without_memory',
    phase_a: {
      prompt: phaseAPrompt,
      response: phaseA.text,
      parsed: phaseA.parsed,
      meta: phaseA.meta,
    },
    phase_b: {
      question: phaseBQuestion,
      response: phaseB.text,
      parsed: phaseBParsed.value,
      meta: phaseBMeta,
    },
    score: scoreTaskContinuity(
      phaseA.parsed.improvements,
      phaseBParsed.value,
      phaseB.text,
      phaseBMeta
    ),
  };
}

async function runDesignDecisionRecallWithMemory(
  client: OllamaClient
): Promise<DesignRecallArm> {
  const dbPath = await createTempDbPath('design-decision-with-memory');
  const memory = new McpMemoryClient(dbPath);
  await memory.start();

  const seededDecisions = buildRetrievalDecisionSeeds();

  try {
    const upserts: unknown[] = [];
    for (const decision of seededDecisions) {
      const payload = {
        text: decision.text,
        kind: 'fact',
        scope: 'project',
        boundary_class: 'internal',
        memory_type: 'knowledge',
        content_hash: sha256(decision.text),
        provenance: {
          at: new Date().toISOString(),
          actor: 'validation-harness',
          note: 'validation/effectiveness experiment2 design decision recall',
        },
      };
      const upsertResult = await memory.callTool('pce_memory_upsert', payload);
      upserts.push(upsertResult);
    }

    const question =
      'What architectural decisions have been made about the retrieval pipeline?';
    const activateArgs = {
      intent: 'design_decision',
      q: 'architectural decisions retrieval pipeline hybrid search',
      scope: ['project'],
      allow: ['answer:task'],
      top_k: 10,
      include_meta: true,
      kind_filter: ['fact'],
      memory_type_filter: ['knowledge'],
    };
    const activateRaw = await memory.callTool('pce_memory_activate', activateArgs);
    const activateSummary = summarizeActivateResult(activateRaw);
    const toolTranscript = buildToolTranscript('pce_memory_activate', activateArgs, activateSummary);

    const answer = await client.chat([
      systemMessage(
        'You are answering a design-decision recall question. Use the provided simulated MCP tool result as the source of truth and do not invent decisions outside that memory.'
      ),
      systemMessage(buildDesignDecisionRecallInstructions()),
      systemMessage(toolTranscript),
      userMessage(question),
    ], {
      jsonMode: true,
      forceJsonSchema: true,
    });
    const parsed = tryParseDecisionRecallPayload(answer.text);
    const meta = mergeMetaInvalidReasons(answer.meta, parsed.invalid_reasons);

    return {
      condition: 'with_memory',
      seeded_decisions: seededDecisions,
      question,
      response: answer.text,
      parsed: parsed.value,
      meta,
      tool_transcript: toolTranscript,
      memory_actions: {
        upserts,
        activate: activateRaw,
      },
      score: scoreDesignDecisionRecall(seededDecisions, parsed.value, answer.text, meta),
    };
  } finally {
    await memory.stop();
  }
}

async function runDesignDecisionRecallWithoutMemory(
  client: OllamaClient
): Promise<DesignRecallArm> {
  const seededDecisions = buildRetrievalDecisionSeeds();
  const question =
    'What architectural decisions have been made about the retrieval pipeline?';
  const answer = await client.chat([
    systemMessage(
      'You are answering from the current conversation only. If you do not have prior architectural context, do not claim that you do.'
    ),
    systemMessage(buildDesignDecisionRecallInstructions()),
    userMessage(question),
  ], {
    jsonMode: true,
    forceJsonSchema: true,
  });
  const parsed = tryParseDecisionRecallPayload(answer.text);
  const meta = mergeMetaInvalidReasons(answer.meta, parsed.invalid_reasons);

  return {
    condition: 'without_memory',
    seeded_decisions: seededDecisions,
    question,
    response: answer.text,
    parsed: parsed.value,
    meta,
    score: scoreDesignDecisionRecall(seededDecisions, parsed.value, answer.text, meta),
  };
}

function systemMessage(content: string): ChatMessage {
  return { role: 'system', content };
}

function userMessage(content: string): ChatMessage {
  return { role: 'user', content };
}

function buildPhaseAAnalyzePrompt(sourceCode: string): string {
  const digest = buildHybridSearchDigest(sourceCode);
  return [
    `Analyze \`${TARGET_FILE_LABEL}\` and identify exactly 3 concrete improvements.`,
    'You are given a grounded digest of the file focused on scoring, filtering, pagination, and vector persistence.',
    'Return JSON only.',
    'Schema:',
    '- Top-level object with key "improvements".',
    '- "improvements" must be an array of exactly 3 objects.',
    '- Each object must contain: "slug" (string), "title" (string), "why" (string), "evidence" (string array).',
    'Rules:',
    '- Make each slug specific and stable.',
    '- Keep each title under 12 words.',
    '- Cite only identifiers, constants, or function names that are present in the file.',
    '- Focus on actionable code improvements rather than style nits.',
    '- Do not emit placeholder text such as "kebab-case-id" or "short title".',
    '',
    `File: ${TARGET_FILE_LABEL}`,
    'Digest:',
    '```ts',
    digest,
    '```',
  ].join('\n');
}

function buildHybridSearchDigest(sourceCode: string): string {
  const lines = sourceCode.split('\n');
  const sections = [
    { label: 'Core constants and validation', start: 38, end: 95 },
    { label: 'Vector search excerpt', start: 570, end: 614 },
    { label: 'Hybrid search scoring and fallback excerpt', start: 940, end: 1056 },
    { label: 'Pagination excerpt', start: 1077, end: 1116 },
    { label: 'Vector persistence excerpt', start: 1189, end: 1204 },
  ];

  return sections
    .map((section) => {
      const excerpt = sliceLines(lines, section.start, section.end);
      return [`// ${section.label} (lines ${section.start}-${section.end})`, excerpt].join('\n');
    })
    .join('\n\n');
}

function sliceLines(lines: string[], startLine: number, endLine: number): string {
  return lines
    .slice(startLine - 1, endLine)
    .join('\n')
    .replace(/\n{3,}/g, '\n\n')
    .trim();
}

function buildTaskContinuityRecallInstructions(): string {
  return [
    'Return JSON only.',
    'Schema:',
    '- status: "ok" or "no_context"',
    '- improvements: array of objects with keys "slug", "explanation", and "evidence"',
    'Rules:',
    '- If prior-session memory is unavailable, return {"status":"no_context","improvements":[]}.',
    '- If memory is available, return status "ok" and copy the exact improvement slugs from memory.',
    '- Keep each explanation to one sentence.',
    '- "evidence" must be an array of strings, not a single comma-separated string.',
    '- Keep evidence entries to concrete identifiers only.',
    '- Do not include markdown, commentary, or reasoning traces.',
  ].join('\n');
}

function buildDesignDecisionRecallInstructions(): string {
  return [
    'Return JSON only.',
    'Schema:',
    '- status: "ok" or "no_context"',
    '- decisions: array of objects with keys "id", "summary", and "params"',
    'Rules:',
    '- If prior architectural memory is unavailable, return {"status":"no_context","decisions":[]}.',
    '- If memory is available, return status "ok" and copy the exact decision ids from memory.',
    '- "params" must be an array of strings, not an object.',
    '- Put concrete parameter names or values in "params".',
    '- Keep each summary to one sentence.',
    '- Do not include markdown, commentary, or reasoning traces.',
  ].join('\n');
}

function parseImprovementPayload(text: string): ImprovementPayload {
  const json = extractFirstJsonObject(text);
  const parsed = JSON.parse(json) as { improvements?: unknown };
  if (!Array.isArray(parsed.improvements) || parsed.improvements.length !== 3) {
    throw new Error(`Expected exactly 3 improvements, got: ${json}`);
  }

  const improvements = parsed.improvements.map((entry, index) => {
    const candidate = entry as Partial<Improvement>;
    const title =
      typeof candidate.title === 'string' && candidate.title.trim().length > 0
        ? candidate.title.trim()
        : `Improvement ${index + 1}`;
    const slug =
      typeof candidate.slug === 'string' && candidate.slug.trim().length > 0
        ? slugify(candidate.slug)
        : slugify(title);
    const why =
      typeof candidate.why === 'string' && candidate.why.trim().length > 0
        ? candidate.why.trim()
        : 'No rationale provided.';
    const evidence = Array.isArray(candidate.evidence)
      ? candidate.evidence
          .filter((value): value is string => typeof value === 'string' && value.trim().length > 0)
          .map((value) => value.trim())
      : [];

    return {
      slug,
      title,
      why,
      evidence,
    };
  });

  return { improvements };
}

function parseImprovementRecallPayload(text: string): ImprovementRecallPayload {
  const json = extractFirstJsonObject(text);
  const parsed = JSON.parse(json) as {
    status?: unknown;
    improvements?: unknown;
  };

  if (parsed.status !== 'ok' && parsed.status !== 'no_context') {
    throw new Error(`Expected status to be "ok" or "no_context", got: ${json}`);
  }
  if (!Array.isArray(parsed.improvements)) {
    throw new Error(`Expected improvements array, got: ${json}`);
  }

  const improvements = parsed.improvements.map((entry, index) => {
    const candidate = entry as Partial<ImprovementRecallItem>;
    if (typeof candidate.slug !== 'string' || candidate.slug.trim().length === 0) {
      throw new Error(`Improvement ${index + 1} is missing slug: ${json}`);
    }
    if (typeof candidate.explanation !== 'string' || candidate.explanation.trim().length === 0) {
      throw new Error(`Improvement ${index + 1} is missing explanation: ${json}`);
    }
    if (!Array.isArray(candidate.evidence)) {
      throw new Error(`Improvement ${index + 1} evidence must be a string array: ${json}`);
    }
    const evidence = candidate.evidence
      .filter((value): value is string => typeof value === 'string' && value.trim().length > 0)
      .map((value) => value.trim());

    return {
      slug: slugify(candidate.slug),
      explanation: candidate.explanation.trim(),
      evidence,
    };
  });

  return {
    status: parsed.status,
    improvements,
  };
}

function parseDecisionRecallPayload(text: string): DecisionRecallPayload {
  const json = extractFirstJsonObject(text);
  const parsed = JSON.parse(json) as {
    status?: unknown;
    decisions?: unknown;
  };

  if (parsed.status !== 'ok' && parsed.status !== 'no_context') {
    throw new Error(`Expected status to be "ok" or "no_context", got: ${json}`);
  }
  if (!Array.isArray(parsed.decisions)) {
    throw new Error(`Expected decisions array, got: ${json}`);
  }

  const decisions = parsed.decisions.map((entry, index) => {
    const candidate = entry as Partial<DecisionRecallItem>;
    if (typeof candidate.id !== 'string' || candidate.id.trim().length === 0) {
      throw new Error(`Decision ${index + 1} is missing id: ${json}`);
    }
    if (typeof candidate.summary !== 'string' || candidate.summary.trim().length === 0) {
      throw new Error(`Decision ${index + 1} is missing summary: ${json}`);
    }
    if (!Array.isArray(candidate.params)) {
      throw new Error(`Decision ${index + 1} params must be a string array: ${json}`);
    }
    const params = candidate.params
      .filter((value): value is string => typeof value === 'string' && value.trim().length > 0)
      .map((value) => value.trim());

    return {
      id: candidate.id.trim(),
      summary: candidate.summary.trim(),
      params,
    };
  });

  return {
    status: parsed.status,
    decisions,
  };
}

function extractFirstJsonObject(text: string): string {
  const start = text.indexOf('{');
  if (start === -1) {
    throw new Error(`No JSON object found in model response: ${text}`);
  }

  let depth = 0;
  let inString = false;
  let escaping = false;
  for (let index = start; index < text.length; index++) {
    const char = text[index];
    if (escaping) {
      escaping = false;
      continue;
    }
    if (char === '\\') {
      escaping = true;
      continue;
    }
    if (char === '"') {
      inString = !inString;
      continue;
    }
    if (inString) {
      continue;
    }
    if (char === '{') {
      depth += 1;
    } else if (char === '}') {
      depth -= 1;
      if (depth === 0) {
        return text.slice(start, index + 1);
      }
    }
  }

  throw new Error(`Unterminated JSON object in model response: ${text}`);
}

function extractCompletionText(payload: ChatCompletionResponse): string {
  const directText = payload.choices?.[0]?.message?.content;
  return typeof directText === 'string' ? directText.trim() : '';
}

function buildCompletionMeta(
  payload: ChatCompletionResponse,
  options: {
    jsonMode: boolean;
  },
  text: string
): CompletionMeta {
  const choice = payload.choices?.[0];
  const finishReason =
    typeof choice?.finish_reason === 'string' && choice.finish_reason.trim().length > 0
      ? choice.finish_reason
      : undefined;
  const hasReasoning =
    typeof choice?.message?.reasoning === 'string' && choice.message.reasoning.trim().length > 0;
  const invalidReasons: string[] = [];

  if (text.length === 0) {
    invalidReasons.push('empty_content');
  }
  if (finishReason === 'length') {
    invalidReasons.push('finish_reason_length');
  }
  if (options.jsonMode && text.length > 0) {
    invalidReasons.push(...detectJsonResponseIssues(text));
  }

  return {
    mode: text.length > 0 ? 'content' : 'empty',
    has_reasoning: hasReasoning,
    finish_reason: finishReason,
    invalid_reasons: [...new Set(invalidReasons)],
  };
}

function detectJsonResponseIssues(text: string): string[] {
  const issues: string[] = [];
  const trimmed = text.trim();

  try {
    const json = extractFirstJsonObject(trimmed);
    if (json !== trimmed) {
      issues.push('non_json_wrapper');
    }
  } catch {
    issues.push('invalid_json_object');
  }

  const normalized = normalizeText(trimmed);
  const leakageMarkers = ['thinking process', '<think>', 'draft analysis', 'reasoning:'];
  if (leakageMarkers.some((marker) => normalized.includes(normalizeText(marker)))) {
    issues.push('reasoning_leakage');
  }

  return [...new Set(issues)];
}

function slugify(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '')
    .replace(/-{2,}/g, '-');
}

function normalizeText(value: string): string {
  return value
    .toLowerCase()
    .replace(/[`*_~]/g, ' ')
    .replace(/[^a-z0-9.]+/g, ' ')
    .replace(/\s+/g, ' ')
    .trim();
}

function computeAnchorScore(answer: string, anchors: string[]): AnchorScore {
  const normalizedAnswer = normalizeText(answer);
  const uniqueAnchors = [...new Set(anchors.filter((anchor) => anchor.trim().length > 0))];
  const matched = uniqueAnchors.filter((anchor) =>
    normalizedAnswer.includes(normalizeText(anchor))
  );
  const missing = uniqueAnchors.filter((anchor) => !matched.includes(anchor));
  return {
    matched,
    missing,
    total: uniqueAnchors.length,
  };
}

function findGenericMarkers(answer: string): string[] {
  const normalizedAnswer = normalizeText(answer);
  const markers = [
    "don't have prior session context",
    'do not have prior session context',
    "i don't know",
    'no prior context',
    'cannot know',
    'without access',
    'generally',
    'typically',
    'in general',
  ];
  return markers.filter((marker) => normalizedAnswer.includes(normalizeText(marker)));
}

function mergeMetaInvalidReasons(meta: CompletionMeta, extra: string[]): CompletionMeta {
  return {
    ...meta,
    invalid_reasons: [...new Set([...meta.invalid_reasons, ...extra])],
  };
}

function tryParseImprovementRecallPayload(
  text: string
): { value?: ImprovementRecallPayload; invalid_reasons: string[] } {
  if (text.trim().length === 0) {
    return { invalid_reasons: ['missing_json_payload'] };
  }

  try {
    return {
      value: parseImprovementRecallPayload(text),
      invalid_reasons: [],
    };
  } catch (error) {
    return {
      invalid_reasons: [
        `improvement_recall_parse_failed:${
          error instanceof Error ? error.message : String(error)
        }`,
      ],
    };
  }
}

function tryParseDecisionRecallPayload(
  text: string
): { value?: DecisionRecallPayload; invalid_reasons: string[] } {
  if (text.trim().length === 0) {
    return { invalid_reasons: ['missing_json_payload'] };
  }

  try {
    return {
      value: parseDecisionRecallPayload(text),
      invalid_reasons: [],
    };
  } catch (error) {
    return {
      invalid_reasons: [
        `decision_recall_parse_failed:${error instanceof Error ? error.message : String(error)}`,
      ],
    };
  }
}

function scoreTaskContinuity(
  improvements: Improvement[],
  payload: ImprovementRecallPayload | undefined,
  answer: string,
  meta: CompletionMeta
): ContinuityScore {
  const recallCorpus = payload
    ? payload.improvements
        .flatMap((improvement) => [
          improvement.slug,
          improvement.explanation,
          ...improvement.evidence,
        ])
        .join('\n')
    : answer;
  const slugScore = computeAnchorScore(
    recallCorpus,
    improvements.map((improvement) => improvement.slug)
  );
  const evidenceScore = computeAnchorScore(
    recallCorpus,
    improvements.flatMap((improvement) => improvement.evidence)
  );
  const genericMarkers = [
    ...(payload?.status === 'no_context' ? ['status:no_context'] : []),
    ...findGenericMarkers(answer),
  ];
  const invalidReasons = [...meta.invalid_reasons];

  if (!payload) {
    invalidReasons.push('missing_or_unparseable_payload');
  } else {
    if (payload.status === 'ok' && payload.improvements.length === 0) {
      invalidReasons.push('ok_without_improvements');
    }
    if (payload.status === 'no_context' && payload.improvements.length > 0) {
      invalidReasons.push('no_context_with_improvements');
    }
  }

  let verdict: ContinuityScore['verdict'] = 'generic_or_no_context';
  if (invalidReasons.length > 0) {
    verdict = 'invalid_response';
  } else if (payload?.status === 'no_context') {
    verdict = 'generic_or_no_context';
  } else if (slugScore.matched.length === improvements.length && improvements.length > 0) {
    verdict = 'specific_recall';
  } else if (slugScore.matched.length >= 1 || evidenceScore.matched.length >= 1) {
    verdict = 'partial_recall';
  }

  return {
    slug_recall: slugScore,
    evidence_recall: evidenceScore,
    generic_markers: genericMarkers,
    invalid_reasons: [...new Set(invalidReasons)],
    verdict,
  };
}

function scoreDesignDecisionRecall(
  decisions: DecisionSeed[],
  payload: DecisionRecallPayload | undefined,
  answer: string,
  meta: CompletionMeta
): DecisionScore {
  const recallCorpus = payload
    ? payload.decisions.flatMap((decision) => [decision.id, decision.summary, ...decision.params]).join('\n')
    : answer;
  const decisionIds = decisions.map((decision) => decision.id);
  const detailAnchors = ['0.65', '0.15', '48', '96', 'alpha', 'threshold', 'k_text', 'k_vec'];
  const decisionIdScore = computeAnchorScore(recallCorpus, decisionIds);
  const detailScore = computeAnchorScore(recallCorpus, detailAnchors);
  const genericMarkers = [
    ...(payload?.status === 'no_context' ? ['status:no_context'] : []),
    ...findGenericMarkers(answer),
  ];
  const invalidReasons = [...meta.invalid_reasons];

  if (!payload) {
    invalidReasons.push('missing_or_unparseable_payload');
  } else {
    if (payload.status === 'ok' && payload.decisions.length === 0) {
      invalidReasons.push('ok_without_decisions');
    }
    if (payload.status === 'no_context' && payload.decisions.length > 0) {
      invalidReasons.push('no_context_with_decisions');
    }
  }

  let verdict: DecisionScore['verdict'] = 'generic_or_no_context';
  if (invalidReasons.length > 0) {
    verdict = 'invalid_response';
  } else if (payload?.status === 'no_context') {
    verdict = 'generic_or_no_context';
  } else if (decisionIdScore.matched.length === decisions.length && detailScore.matched.length >= 3) {
    verdict = 'specific_recall';
  } else if (decisionIdScore.matched.length >= 1 || detailScore.matched.length >= 1) {
    verdict = 'partial_recall';
  }

  return {
    decision_id_recall: decisionIdScore,
    detail_recall: detailScore,
    generic_markers: genericMarkers,
    invalid_reasons: [...new Set(invalidReasons)],
    verdict,
  };
}

function formatImprovementClaim(improvement: Improvement): string {
  const evidence =
    improvement.evidence.length > 0 ? ` Evidence: ${improvement.evidence.join(', ')}.` : '';
  return `${TARGET_FILE_LABEL} improvement ${improvement.slug}: ${improvement.why}${evidence}`;
}

function summarizeActivateResult(result: unknown): unknown {
  const payload = result as {
    claims?: Array<{
      claim?: {
        id?: string;
        text?: string;
        kind?: string;
        scope?: string;
        memory_type?: string | null;
      };
      score?: number;
      rank?: number;
      source_layer?: string;
    }>;
    claims_count?: number;
    active_context_id?: string;
    state?: string;
  };

  return {
    active_context_id: payload.active_context_id,
    claims_count: payload.claims_count,
    state: payload.state,
    claims: Array.isArray(payload.claims)
      ? payload.claims.map((item) => ({
          id: item.claim?.id,
          text: item.claim?.text,
        }))
      : [],
  };
}

function buildToolTranscript(
  toolName: string,
  args: Record<string, unknown>,
  result: unknown
): string {
  const payload = result as {
    active_context_id?: string;
    claims_count?: number;
    claims?: Array<{ id?: string; text?: string }>;
  };
  const claimLines =
    payload.claims && payload.claims.length > 0
      ? payload.claims.map((claim) => `- ${claim.text ?? claim.id ?? 'unknown claim'}`)
      : ['- none'];

  return [
    `Simulated MCP tool result from ${toolName}.`,
    `Query: ${typeof args.q === 'string' ? args.q : 'n/a'}`,
    `Active context: ${payload.active_context_id ?? 'n/a'}`,
    `Claims returned: ${payload.claims_count ?? claimLines.length}`,
    'Relevant memory claims:',
    ...claimLines,
  ].join('\n');
}

function buildRetrievalDecisionSeeds(): DecisionSeed[] {
  return [
    {
      id: 'retrieval-alpha-0-65-vector-bias',
      text: [
        'decision_id=retrieval-alpha-0-65-vector-bias',
        'The retrieval pipeline fuses text and vector scores with ALPHA=0.65, intentionally biasing ranking toward vector search results.',
      ].join('; '),
    },
    {
      id: 'retrieval-threshold-0-15-noise-gate',
      text: [
        'decision_id=retrieval-threshold-0-15-noise-gate',
        'The retrieval pipeline applies THRESHOLD=0.15 to suppress low-signal candidates before the final result set is returned.',
      ].join('; '),
    },
    {
      id: 'retrieval-candidate-pools-48-96',
      text: [
        'decision_id=retrieval-candidate-pools-48-96',
        'The retrieval pipeline expands recall with K_TEXT=48 and K_VEC=96 candidate pools before merge and reranking.',
      ].join('; '),
    },
  ];
}

function sha256(value: string): string {
  return `sha256:${createHash('sha256').update(value).digest('hex')}`;
}

async function createTempDbPath(prefix: string): Promise<string> {
  const dir = await fs.mkdtemp(path.join(tmpdir(), `pce-memory-${prefix}-`));
  return path.join(dir, 'memory.duckdb');
}

async function fetchWithTimeout(url: string, init: RequestInit): Promise<Response> {
  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), CHAT_TIMEOUT_MS);

  try {
    const response = await fetch(url, {
      ...init,
      signal: controller.signal,
    });
    if (!response.ok) {
      const body = await response.text();
      throw new Error(`HTTP ${response.status} for ${url}: ${body}`);
    }
    return response;
  } finally {
    clearTimeout(timeout);
  }
}

function buildReport(results: ExperimentResults): string {
  const experiment1 = results.experiments.task_continuity;
  const experiment2 = results.experiments.design_decision_recall;

  return [
    '# Local LLM Effectiveness Report',
    '',
    `Generated: ${results.generated_at}`,
    '',
    '## Configuration',
    '',
    `- Ollama endpoint: \`${results.configuration.ollama_chat_url}\``,
    `- Ollama models endpoint: \`${results.configuration.ollama_models_url}\``,
    `- Model: \`${results.configuration.model}\``,
    `- Max tokens: \`${results.configuration.max_tokens}\``,
    `- JSON retry max tokens: \`${results.configuration.json_retry_max_tokens}\``,
    `- Reasoning effort: \`${results.configuration.reasoning_effort}\``,
    `- Temperature: \`${results.configuration.temperature}\``,
    `- Target file: \`${results.configuration.target_file}\``,
    `- MCP server: \`${results.configuration.mcp_server}\``,
    '',
    '## Preflight',
    '',
    `- Available models: ${results.preflight.available_models.map((model) => `\`${model}\``).join(', ')}`,
    '',
    '## Experiment 1: Task Continuity',
    '',
    `- WITH-MEMORY verdict: \`${experiment1.with_memory.score.verdict}\``,
    `- WITH-MEMORY slug recall: ${experiment1.with_memory.score.slug_recall.matched.length}/${experiment1.with_memory.score.slug_recall.total}`,
    `- WITH-MEMORY invalid reasons: ${formatInlineList(experiment1.with_memory.score.invalid_reasons)}`,
    `- WITHOUT-MEMORY verdict: \`${experiment1.without_memory.score.verdict}\``,
    `- WITHOUT-MEMORY slug recall: ${experiment1.without_memory.score.slug_recall.matched.length}/${experiment1.without_memory.score.slug_recall.total}`,
    `- WITHOUT-MEMORY invalid reasons: ${formatInlineList(experiment1.without_memory.score.invalid_reasons)}`,
    '',
    '### WITH-MEMORY recovered slugs',
    '',
    ...renderFlatList(experiment1.with_memory.score.slug_recall.matched),
    '',
    '### WITHOUT-MEMORY missing slugs',
    '',
    ...renderFlatList(experiment1.without_memory.score.slug_recall.missing),
    '',
    '### WITH-MEMORY Phase B answer',
    '',
    '```text',
    experiment1.with_memory.phase_b.response,
    '```',
    '',
    '### WITHOUT-MEMORY Phase B answer',
    '',
    '```text',
    experiment1.without_memory.phase_b.response,
    '```',
    '',
    '## Experiment 2: Design Decision Recall',
    '',
    `- WITH-MEMORY verdict: \`${experiment2.with_memory.score.verdict}\``,
    `- WITH-MEMORY decision recall: ${experiment2.with_memory.score.decision_id_recall.matched.length}/${experiment2.with_memory.score.decision_id_recall.total}`,
    `- WITH-MEMORY invalid reasons: ${formatInlineList(experiment2.with_memory.score.invalid_reasons)}`,
    `- WITHOUT-MEMORY verdict: \`${experiment2.without_memory.score.verdict}\``,
    `- WITHOUT-MEMORY decision recall: ${experiment2.without_memory.score.decision_id_recall.matched.length}/${experiment2.without_memory.score.decision_id_recall.total}`,
    `- WITHOUT-MEMORY invalid reasons: ${formatInlineList(experiment2.without_memory.score.invalid_reasons)}`,
    '',
    '### WITH-MEMORY recovered decision ids',
    '',
    ...renderFlatList(experiment2.with_memory.score.decision_id_recall.matched),
    '',
    '### WITHOUT-MEMORY missing decision ids',
    '',
    ...renderFlatList(experiment2.without_memory.score.decision_id_recall.missing),
    '',
    '### WITH-MEMORY answer',
    '',
    '```text',
    experiment2.with_memory.response,
    '```',
    '',
    '### WITHOUT-MEMORY answer',
    '',
    '```text',
    experiment2.without_memory.response,
    '```',
    '',
    '## Takeaway',
    '',
    `- Experiment 1 shows whether persisted memory can recover prior session findings instead of forcing the model to answer from scratch.`,
    `- Experiment 2 shows whether explicit architectural decisions are recalled with concrete ids and parameter values once they are stored in pce-memory.`,
    '',
  ].join('\n');
}

function renderFlatList(items: string[]): string[] {
  if (items.length === 0) {
    return ['- none'];
  }
  return items.map((item) => `- \`${item}\``);
}

function formatInlineList(items: string[]): string {
  return items.length > 0 ? items.map((item) => `\`${item}\``).join(', ') : 'none';
}

function parsePositiveInt(value: string | undefined): number | undefined {
  if (!value) {
    return undefined;
  }
  const parsed = Number.parseInt(value, 10);
  return Number.isInteger(parsed) && parsed > 0 ? parsed : undefined;
}

main().catch((error) => {
  console.error(error instanceof Error ? error.stack ?? error.message : String(error));
  process.exit(1);
});

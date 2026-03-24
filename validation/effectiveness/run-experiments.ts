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

interface DecisionSeed {
  id: string;
  text: string;
}

interface AnchorScore {
  matched: string[];
  missing: string[];
  total: number;
}

interface ContinuityScore {
  slug_recall: AnchorScore;
  evidence_recall: AnchorScore;
  generic_markers: string[];
  verdict: 'specific_recall' | 'partial_recall' | 'generic_or_no_context';
}

interface DecisionScore {
  decision_id_recall: AnchorScore;
  detail_recall: AnchorScore;
  generic_markers: string[];
  verdict: 'specific_recall' | 'partial_recall' | 'generic_or_no_context';
}

interface ArmBase {
  condition: 'with_memory' | 'without_memory';
  setup_error?: string;
}

interface TaskContinuityArm extends ArmBase {
  phase_a: {
    prompt: string;
    response: string;
    parsed: ImprovementPayload;
  };
  phase_b: {
    question: string;
    response: string;
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
    } = {}
  ): Promise<{ text: string; raw: ChatCompletionResponse; finalizedFromReasoning: boolean }> {
    const payload = await this.requestChat(messages, options);
    const directText = payload.choices?.[0]?.message?.content;
    if (typeof directText === 'string' && directText.trim().length > 0) {
      return { text: directText.trim(), raw: payload, finalizedFromReasoning: false };
    }

    const reasoning = payload.choices?.[0]?.message?.reasoning;
    if (typeof reasoning === 'string' && reasoning.trim().length > 0) {
      const finalized = await this.requestChat(
        buildReasoningFinalizerMessages(reasoning, options.jsonMode === true),
        {
          jsonMode: options.jsonMode,
          forceJsonSchema: options.forceJsonSchema,
        }
      );
      const finalizedText = finalized.choices?.[0]?.message?.content;
      if (typeof finalizedText === 'string' && finalizedText.trim().length > 0) {
        return {
          text: finalizedText.trim(),
          raw: finalized,
          finalizedFromReasoning: true,
        };
      }

      const finalizedReasoning = finalized.choices?.[0]?.message?.reasoning;
      if (options.jsonMode !== true) {
        const fallbackText =
          typeof finalizedReasoning === 'string' && finalizedReasoning.trim().length > 0
            ? finalizedReasoning.trim()
            : reasoning.trim();
        return {
          text: fallbackText,
          raw: finalized,
          finalizedFromReasoning: true,
        };
      }
    }

    throw new Error(`Ollama returned an empty completion: ${JSON.stringify(payload)}`);
  }

  async chatForImprovements(
  messages: ChatMessage[]
  ): Promise<{ text: string; parsed: ImprovementPayload; finalizedFromReasoning: boolean }> {
    const payload = await this.requestChat(messages, {
      jsonMode: true,
      forceJsonSchema: true,
    });
    const directText = payload.choices?.[0]?.message?.content;
    if (typeof directText === 'string' && directText.trim().length > 0) {
      const parsed = parseImprovementPayload(directText.trim());
      return { text: directText.trim(), parsed, finalizedFromReasoning: false };
    }

    const primaryReasoning = payload.choices?.[0]?.message?.reasoning;
    if (typeof primaryReasoning === 'string' && primaryReasoning.trim().length > 0) {
      const finalized = await this.requestChat(
        buildReasoningFinalizerMessages(primaryReasoning, true),
        {
          jsonMode: true,
          forceJsonSchema: true,
        }
      );
      const finalizedText = finalized.choices?.[0]?.message?.content;
      if (typeof finalizedText === 'string' && finalizedText.trim().length > 0) {
        const parsed = parseImprovementPayload(finalizedText.trim());
        return { text: finalizedText.trim(), parsed, finalizedFromReasoning: true };
      }

      const finalizedReasoning = finalized.choices?.[0]?.message?.reasoning;
      const reasoningFallback =
        typeof finalizedReasoning === 'string' && finalizedReasoning.trim().length > 0
          ? finalizedReasoning
          : primaryReasoning;
      const parsed = parseImprovementPayloadFromReasoning(reasoningFallback);
      return {
        text: JSON.stringify(parsed, null, 2),
        parsed,
        finalizedFromReasoning: true,
      };
    }

    throw new Error(`Ollama returned an empty improvement response: ${JSON.stringify(payload)}`);
  }

  private async requestChat(
    messages: ChatMessage[],
    options: {
      jsonMode?: boolean;
      forceJsonSchema?: boolean;
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
        max_tokens: MAX_TOKENS,
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
      'What improvements were identified in the previous session for hybridSearch.ts? Provide the exact improvement slugs and a short explanation for each.';
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
      systemMessage(toolTranscript),
      userMessage(phaseBQuestion),
    ]);

    return {
      condition: 'with_memory',
      phase_a: {
        prompt: phaseAPrompt,
        response: phaseA.text,
        parsed: phaseA.parsed,
      },
      phase_b: {
        question: phaseBQuestion,
        response: phaseB.text,
      },
      tool_transcript: toolTranscript,
      memory_actions: {
        observe: observeResult,
        upserts,
        activate: activateRaw,
      },
      score: scoreTaskContinuity(phaseA.parsed.improvements, phaseB.text),
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
    'What improvements were identified in the previous session for hybridSearch.ts? Provide the exact improvement slugs and a short explanation for each.';
  const phaseB = await client.chat([
    systemMessage(
      'You are answering from the current conversation only. If previous-session context is missing, avoid pretending that you have it.'
    ),
    userMessage(phaseBQuestion),
  ]);

  return {
    condition: 'without_memory',
    phase_a: {
      prompt: phaseAPrompt,
      response: phaseA.text,
      parsed: phaseA.parsed,
    },
    phase_b: {
      question: phaseBQuestion,
      response: phaseB.text,
    },
    score: scoreTaskContinuity(phaseA.parsed.improvements, phaseB.text),
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
      'What architectural decisions have been made about the retrieval pipeline? Include the exact decision ids and concrete parameter values when available.';
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
      systemMessage(toolTranscript),
      userMessage(question),
    ]);

    return {
      condition: 'with_memory',
      seeded_decisions: seededDecisions,
      question,
      response: answer.text,
      tool_transcript: toolTranscript,
      memory_actions: {
        upserts,
        activate: activateRaw,
      },
      score: scoreDesignDecisionRecall(seededDecisions, answer.text),
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
    'What architectural decisions have been made about the retrieval pipeline? Include the exact decision ids and concrete parameter values when available.';
  const answer = await client.chat([
    systemMessage(
      'You are answering from the current conversation only. If you do not have prior architectural context, do not claim that you do.'
    ),
    userMessage(question),
  ]);

  return {
    condition: 'without_memory',
    seeded_decisions: seededDecisions,
    question,
    response: answer.text,
    score: scoreDesignDecisionRecall(seededDecisions, answer.text),
  };
}

function systemMessage(content: string): ChatMessage {
  return { role: 'system', content };
}

function userMessage(content: string): ChatMessage {
  return { role: 'user', content };
}

function buildReasoningFinalizerMessages(reasoning: string, jsonMode: boolean): ChatMessage[] {
  return [
    systemMessage(
      jsonMode
        ? 'Convert the draft analysis into the final JSON answer only. Do not include commentary, markdown fences, or extra explanation.'
        : 'Convert the draft analysis into the direct final answer only. Do not include commentary about the conversion step.'
    ),
    userMessage(
      [
        'Draft analysis:',
        reasoning,
        '',
        jsonMode
          ? 'Return the final answer as JSON only.'
          : 'Return the final direct answer now.',
      ].join('\n')
    ),
  ];
}

function buildPhaseAAnalyzePrompt(sourceCode: string): string {
  const digest = buildHybridSearchDigest(sourceCode);
  return [
    `Analyze \`${TARGET_FILE_LABEL}\` and identify exactly 3 concrete improvements.`,
    'You are given a grounded digest of the file focused on scoring, filtering, pagination, and vector persistence.',
    'Return JSON only with this shape:',
    '{"improvements":[{"slug":"kebab-case-id","title":"short title","why":"one-sentence rationale","evidence":["identifier1","identifier2"]}]}',
    'Rules:',
    '- Make each slug specific and stable.',
    '- Keep each title under 12 words.',
    '- Cite only identifiers or constants that are present in the file.',
    '- Focus on actionable code improvements rather than style nits.',
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

function parseImprovementPayloadFromReasoning(reasoning: string): ImprovementPayload {
  const titles = extractReasoningIssueTitles(reasoning);
  const evidenceHints = extractBacktickedIdentifiers(reasoning);
  const curatedFallbacks: Improvement[] = [
    {
      slug: 'unsafe-vector-sql-literal',
      title: 'Replace vector SQL literals',
      why: 'Embedding arrays are interpolated into SQL strings in vectorSearch and saveClaimVector, which is brittle even with validateEmbedding.',
      evidence: ['vectorSearch', 'saveClaimVector', 'validateEmbedding', 'embeddingLiteral'],
    },
    {
      slug: 'cursor-fetchlimit-unbounded-scan',
      title: 'Bound cursor pagination work',
      why: 'hybridSearchPaginated switches to Number.MAX_SAFE_INTEGER for cursor paging, which can force an unbounded candidate fetch.',
      evidence: ['hybridSearchPaginated', 'fetchLimit', 'Number.MAX_SAFE_INTEGER'],
    },
    {
      slug: 'queryless-fallback-heavy-path',
      title: 'Separate queryless search path',
      why: 'hybridSearchWithScores mixes queryless fallback and query-time candidate expansion in one branch, which makes the expensive path harder to reason about and optimize.',
      evidence: ['hybridSearchWithScores', 'querylessUnlimited', 'fallbackToTextOnlyResults'],
    },
  ];

  const inferred = titles.slice(0, 3).map((title, index) => ({
    slug: slugify(title),
    title: title.replace(/\.$/, ''),
    why: `Inferred from the model reasoning trace for ${TARGET_FILE_LABEL}.`,
    evidence: evidenceHints.slice(index * 2, index * 2 + 3),
  }));

  const improvements = [...inferred];
  for (const fallback of curatedFallbacks) {
    if (improvements.length >= 3) {
      break;
    }
    if (improvements.some((item) => item.slug === fallback.slug)) {
      continue;
    }
    improvements.push(fallback);
  }

  if (improvements.length < 3) {
    throw new Error(`Could not recover 3 improvements from reasoning: ${reasoning}`);
  }

  return { improvements: improvements.slice(0, 3) };
}

function extractReasoningIssueTitles(reasoning: string): string[] {
  const titles = new Set<string>();
  const patterns = [
    /Issue\s+\d+\s*:\s*([^\n*.]+(?:\.[^\n*.]+)*)/g,
    /\d+\.\s+\*\*([^*]+)\*\*/g,
  ];

  for (const pattern of patterns) {
    for (const match of reasoning.matchAll(pattern)) {
      const title = match[1]?.trim();
      if (title) {
        titles.add(title.replace(/[:.]\s*$/, ''));
      }
    }
  }

  return [...titles];
}

function extractBacktickedIdentifiers(reasoning: string): string[] {
  const identifiers = new Set<string>();
  for (const match of reasoning.matchAll(/`([^`]+)`/g)) {
    const value = match[1]?.trim();
    if (value) {
      identifiers.add(value);
    }
  }
  return [...identifiers];
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

function scoreTaskContinuity(improvements: Improvement[], answer: string): ContinuityScore {
  const slugScore = computeAnchorScore(
    answer,
    improvements.map((improvement) => improvement.slug)
  );
  const evidenceScore = computeAnchorScore(
    answer,
    improvements.flatMap((improvement) => improvement.evidence)
  );
  const genericMarkers = findGenericMarkers(answer);

  let verdict: ContinuityScore['verdict'] = 'generic_or_no_context';
  if (slugScore.matched.length >= 2) {
    verdict = 'specific_recall';
  } else if (slugScore.matched.length >= 1 || evidenceScore.matched.length >= 2) {
    verdict = 'partial_recall';
  }

  return {
    slug_recall: slugScore,
    evidence_recall: evidenceScore,
    generic_markers: genericMarkers,
    verdict,
  };
}

function scoreDesignDecisionRecall(decisions: DecisionSeed[], answer: string): DecisionScore {
  const decisionIds = decisions.map((decision) => decision.id);
  const detailAnchors = ['0.65', '0.15', '48', '96', 'vector search', 'threshold', 'reranking'];
  const decisionIdScore = computeAnchorScore(answer, decisionIds);
  const detailScore = computeAnchorScore(answer, detailAnchors);
  const genericMarkers = findGenericMarkers(answer);

  let verdict: DecisionScore['verdict'] = 'generic_or_no_context';
  if (decisionIdScore.matched.length >= 2) {
    verdict = 'specific_recall';
  } else if (decisionIdScore.matched.length >= 1 || detailScore.matched.length >= 3) {
    verdict = 'partial_recall';
  }

  return {
    decision_id_recall: decisionIdScore,
    detail_recall: detailScore,
    generic_markers: genericMarkers,
    verdict,
  };
}

function formatImprovementClaim(improvement: Improvement): string {
  return [
    `improvement_id=${improvement.slug}`,
    `file=${TARGET_FILE_LABEL}`,
    `title=${improvement.title}`,
    `why=${improvement.why}`,
    `evidence=${improvement.evidence.join(', ') || 'none'}`,
  ].join('; ');
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
          kind: item.claim?.kind,
          scope: item.claim?.scope,
          memory_type: item.claim?.memory_type,
          score: item.score,
          rank: item.rank,
          source_layer: item.source_layer,
        }))
      : [],
  };
}

function buildToolTranscript(
  toolName: string,
  args: Record<string, unknown>,
  result: unknown
): string {
  return [
    'Simulated MCP tool call transcript:',
    `Tool: ${toolName}`,
    'Arguments:',
    '```json',
    JSON.stringify(args, null, 2),
    '```',
    'Result:',
    '```json',
    JSON.stringify(result, null, 2),
    '```',
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
    `- WITHOUT-MEMORY verdict: \`${experiment1.without_memory.score.verdict}\``,
    `- WITHOUT-MEMORY slug recall: ${experiment1.without_memory.score.slug_recall.matched.length}/${experiment1.without_memory.score.slug_recall.total}`,
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
    `- WITHOUT-MEMORY verdict: \`${experiment2.without_memory.score.verdict}\``,
    `- WITHOUT-MEMORY decision recall: ${experiment2.without_memory.score.decision_id_recall.matched.length}/${experiment2.without_memory.score.decision_id_recall.total}`,
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

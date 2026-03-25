import type { EntityInput } from './entities.js';

export interface EntityCandidate {
  type: EntityInput['type'];
  name: string;
  canonical_key: string;
  attrs?: Record<string, unknown>;
}

export interface RelationCandidate {
  src: string;
  dst: string;
  type: string;
  props?: Record<string, unknown>;
}

interface OllamaChatResponse {
  choices?: Array<{
    message?: {
      content?: string | null;
    };
  }>;
}

const EMPTY_RESULT = Object.freeze({
  entities: [] as EntityCandidate[],
  relations: [] as RelationCandidate[],
});

export const DEFAULT_OLLAMA_ENDPOINT = 'http://127.0.0.1:11434';
export const DEFAULT_OLLAMA_MODEL = 'qwen3.5:9b';
export const LLM_EXTRACTION_TIMEOUT_MS = 5_000;

function isPlainObject(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null && !Array.isArray(value);
}

function normalizeWhitespace(value: string): string {
  return value.replace(/\s+/g, ' ').trim();
}

function normalizeCanonicalKey(value: string): string {
  return normalizeWhitespace(value)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, '-')
    .replace(/^-+|-+$/g, '');
}

function normalizeRelationType(value: string): string {
  return normalizeWhitespace(value)
    .toUpperCase()
    .replace(/[^A-Z0-9]+/g, '_')
    .replace(/^_+|_+$/g, '');
}

function normalizeEntityType(raw: string): EntityInput['type'] | undefined {
  const normalized = normalizeCanonicalKey(raw);
  switch (normalized) {
    case 'actor':
    case 'person':
    case 'people':
    case 'user':
    case 'team':
    case 'organization':
    case 'org':
    case 'company':
      return 'Actor';
    case 'artifact':
    case 'technology':
    case 'tool':
    case 'library':
    case 'framework':
    case 'package':
    case 'service':
    case 'api':
    case 'database':
    case 'file':
    case 'config':
    case 'configuration':
      return 'Artifact';
    case 'event':
    case 'incident':
    case 'release':
    case 'migration':
    case 'deployment':
      return 'Event';
    case 'concept':
    case 'architecture':
    case 'pattern':
    case 'policy':
    case 'workflow':
    case 'knowledge':
      return 'Concept';
    default:
      return raw === 'Actor' || raw === 'Artifact' || raw === 'Event' || raw === 'Concept'
        ? raw
        : undefined;
  }
}

function resolveOllamaUrl(endpoint: string): string {
  const trimmed = endpoint.trim().replace(/\/+$/g, '');
  if (trimmed.endsWith('/v1/chat/completions')) {
    return trimmed;
  }
  if (trimmed.endsWith('/chat/completions')) {
    return `${trimmed.slice(0, -'/chat/completions'.length)}/v1/chat/completions`;
  }
  return `${trimmed}/v1/chat/completions`;
}

function extractJsonCandidate(content: string): unknown {
  const direct = content.trim();
  if (direct.length === 0) {
    return null;
  }

  try {
    return JSON.parse(direct) as unknown;
  } catch {
    // fall through
  }

  const fencedMatch = direct.match(/```(?:json)?\s*([\s\S]*?)```/i);
  if (fencedMatch?.[1]) {
    try {
      return JSON.parse(fencedMatch[1]) as unknown;
    } catch {
      // fall through
    }
  }

  const firstBrace = direct.indexOf('{');
  const lastBrace = direct.lastIndexOf('}');
  if (firstBrace >= 0 && lastBrace > firstBrace) {
    try {
      return JSON.parse(direct.slice(firstBrace, lastBrace + 1)) as unknown;
    } catch {
      return null;
    }
  }

  return null;
}

function normalizeEntityCandidate(value: unknown): EntityCandidate | undefined {
  if (!isPlainObject(value)) {
    return undefined;
  }

  const rawName =
    typeof value['name'] === 'string'
      ? value['name']
      : typeof value['label'] === 'string'
        ? value['label']
        : undefined;
  const rawType =
    typeof value['type'] === 'string'
      ? value['type']
      : typeof value['category'] === 'string'
        ? value['category']
        : undefined;
  if (!rawName || !rawType) {
    return undefined;
  }

  const name = normalizeWhitespace(rawName);
  const type = normalizeEntityType(rawType);
  if (name.length === 0 || !type) {
    return undefined;
  }

  const rawCanonicalKey =
    typeof value['canonical_key'] === 'string'
      ? value['canonical_key']
      : typeof value['canonicalKey'] === 'string'
        ? value['canonicalKey']
        : name;
  const canonicalKey = normalizeCanonicalKey(rawCanonicalKey);
  if (canonicalKey.length === 0) {
    return undefined;
  }

  const attrs = isPlainObject(value['attrs'])
    ? value['attrs']
    : isPlainObject(value['metadata'])
      ? value['metadata']
      : undefined;

  return {
    type,
    name,
    canonical_key: canonicalKey,
    ...(attrs ? { attrs } : {}),
  };
}

function normalizeRelationCandidate(
  value: unknown,
  aliases: Map<string, string>
): RelationCandidate | undefined {
  if (!isPlainObject(value)) {
    return undefined;
  }

  const rawSrc =
    typeof value['src'] === 'string'
      ? value['src']
      : typeof value['source'] === 'string'
        ? value['source']
        : typeof value['from'] === 'string'
          ? value['from']
          : undefined;
  const rawDst =
    typeof value['dst'] === 'string'
      ? value['dst']
      : typeof value['target'] === 'string'
        ? value['target']
        : typeof value['to'] === 'string'
          ? value['to']
          : undefined;
  const rawType =
    typeof value['type'] === 'string'
      ? value['type']
      : typeof value['relation'] === 'string'
        ? value['relation']
        : undefined;
  if (!rawSrc || !rawDst || !rawType) {
    return undefined;
  }

  const srcKey = aliases.get(normalizeCanonicalKey(rawSrc));
  const dstKey = aliases.get(normalizeCanonicalKey(rawDst));
  const relationType = normalizeRelationType(rawType);
  if (!srcKey || !dstKey || srcKey === dstKey || relationType.length === 0) {
    return undefined;
  }

  const props = isPlainObject(value['props'])
    ? value['props']
    : isPlainObject(value['metadata'])
      ? value['metadata']
      : undefined;

  return {
    src: srcKey,
    dst: dstKey,
    type: relationType,
    ...(props ? { props } : {}),
  };
}

function mergeEntityCandidate(
  current: EntityCandidate | undefined,
  next: EntityCandidate
): EntityCandidate {
  if (!current) {
    return next;
  }

  const mergedAttrs =
    current.attrs || next.attrs ? { ...(current.attrs ?? {}), ...(next.attrs ?? {}) } : undefined;
  return {
    type: current.type,
    name: next.name.length > current.name.length ? next.name : current.name,
    canonical_key: current.canonical_key,
    ...(mergedAttrs ? { attrs: mergedAttrs } : {}),
  };
}

function stableJson(value: unknown): string {
  if (Array.isArray(value)) {
    return `[${value.map((item) => stableJson(item)).join(',')}]`;
  }
  if (isPlainObject(value)) {
    return `{${Object.keys(value)
      .sort()
      .map((key) => `${JSON.stringify(key)}:${stableJson(value[key])}`)
      .join(',')}}`;
  }
  return JSON.stringify(value);
}

function normalizeExtractionPayload(payload: unknown): {
  entities: EntityCandidate[];
  relations: RelationCandidate[];
} {
  if (!isPlainObject(payload)) {
    return EMPTY_RESULT;
  }

  const entityMap = new Map<string, EntityCandidate>();
  const aliases = new Map<string, string>();

  if (Array.isArray(payload['entities'])) {
    for (const rawEntity of payload['entities']) {
      const entity = normalizeEntityCandidate(rawEntity);
      if (!entity) {
        continue;
      }

      entityMap.set(entity.canonical_key, mergeEntityCandidate(entityMap.get(entity.canonical_key), entity));
      aliases.set(entity.canonical_key, entity.canonical_key);
      aliases.set(normalizeCanonicalKey(entity.name), entity.canonical_key);
    }
  }

  const relations: RelationCandidate[] = [];
  const seenRelations = new Set<string>();
  if (Array.isArray(payload['relations'])) {
    for (const rawRelation of payload['relations']) {
      const relation = normalizeRelationCandidate(rawRelation, aliases);
      if (!relation) {
        continue;
      }

      const dedupeKey = `${relation.src}|${relation.type}|${relation.dst}|${stableJson(relation.props ?? null)}`;
      if (seenRelations.has(dedupeKey)) {
        continue;
      }
      seenRelations.add(dedupeKey);
      relations.push(relation);
    }
  }

  return {
    entities: [...entityMap.values()],
    relations,
  };
}

function buildPrompt(text: string): string {
  return [
    'Extract named entities (technology, file, concept, person, config) and their relations from this text. Return JSON.',
    'Use this exact shape: {"entities":[{"name":"...","type":"Actor|Artifact|Event|Concept","canonical_key":"...","attrs":{}}],"relations":[{"src":"entity canonical_key or name","dst":"entity canonical_key or name","type":"USES|DEPENDS_ON|CONFIGURES|RELATES_TO","props":{}}]}.',
    'Map person/team/org to Actor, technology/file/config/service/library/framework to Artifact, dated incident/release/migration to Event, and abstract ideas/policies/architectures to Concept.',
    'Return JSON only. Do not include explanations or markdown.',
    '',
    'Text:',
    text,
  ].join('\n');
}

export async function extractEntitiesWithLLM(
  text: string,
  opts: { ollamaEndpoint?: string; model?: string } = {}
): Promise<{ entities: EntityCandidate[]; relations: RelationCandidate[] }> {
  const trimmedText = text.trim();
  if (trimmedText.length === 0) {
    return EMPTY_RESULT;
  }

  const controller = new AbortController();
  const timeout = setTimeout(() => controller.abort(), LLM_EXTRACTION_TIMEOUT_MS);

  try {
    const response = await fetch(resolveOllamaUrl(opts.ollamaEndpoint ?? DEFAULT_OLLAMA_ENDPOINT), {
      method: 'POST',
      headers: {
        'content-type': 'application/json',
      },
      body: JSON.stringify({
        model: opts.model ?? DEFAULT_OLLAMA_MODEL,
        stream: false,
        temperature: 0,
        messages: [
          {
            role: 'system',
            content:
              'You extract technical knowledge-graph entities and relations. Always return valid JSON.',
          },
          {
            role: 'user',
            content: buildPrompt(trimmedText),
          },
        ],
      }),
      signal: controller.signal,
    });

    if (!response.ok) {
      return EMPTY_RESULT;
    }

    const payload = (await response.json()) as OllamaChatResponse;
    const content = payload.choices?.[0]?.message?.content;
    if (typeof content !== 'string' || content.trim().length === 0) {
      return EMPTY_RESULT;
    }

    const parsed = extractJsonCandidate(content);
    return normalizeExtractionPayload(parsed);
  } catch {
    return EMPTY_RESULT;
  } finally {
    clearTimeout(timeout);
  }
}

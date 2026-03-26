import type {
  PolicyDocument,
  BoundaryPolicy,
  TopologyPolicy,
  ValidationResult,
} from './types.js';

function isString(x: unknown): x is string {
  return typeof x === 'string';
}

function ensureString(field: string, val: unknown, errors: string[]) {
  if (!isString(val)) errors.push(`${field} must be string`);
}

function ensureBoolean(field: string, val: unknown, errors: string[]) {
  if (typeof val !== 'boolean') errors.push(`${field} must be boolean`);
}

function ensureNumber(field: string, val: unknown, errors: string[]) {
  if (typeof val !== 'number' || Number.isNaN(val)) errors.push(`${field} must be number`);
}

function ensureInteger(field: string, val: unknown, errors: string[]) {
  ensureNumber(field, val, errors);
  if (typeof val === 'number' && Number.isFinite(val) && !Number.isInteger(val)) {
    errors.push(`${field} must be integer`);
  }
}

function ensureEnum<T extends string>(
  field: string,
  val: unknown,
  allowed: readonly T[],
  errors: string[]
) {
  if (typeof val !== 'string' || !allowed.includes(val as T)) {
    errors.push(`${field} must be one of ${allowed.join(', ')}`);
  }
}

function ensureObject(field: string, val: unknown, errors: string[]) {
  if (!val || typeof val !== 'object' || Array.isArray(val)) {
    errors.push(`${field} must be object`);
  }
}

function rejectUnknownKeys(
  field: string,
  input: Record<string, unknown>,
  allowedKeys: readonly string[],
  errors: string[]
): void {
  const allowed = new Set(allowedKeys);
  for (const key of Object.keys(input)) {
    if (!allowed.has(key)) {
      errors.push(`${field}.${key} is not allowed`);
    }
  }
}

function validateTopologyPolicy(input: Record<string, unknown>): ValidationResult<TopologyPolicy> {
  const errors: string[] = [];
  ensureObject('retrieval.hybrid.topology', input, errors);
  if (errors.length > 0) {
    return { ok: false, errors };
  }

  const allowedKeys = ['enabled', 'mode', 'seed_k', 'max_hops', 'hop_decay', 'include_paths', 'edge_policy'];
  rejectUnknownKeys('retrieval.hybrid.topology', input, allowedKeys, errors);

  if (input['enabled'] !== undefined) ensureBoolean('topology.enabled', input['enabled'], errors);
  if (input['mode'] !== undefined) {
    ensureEnum('topology.mode', input['mode'], ['walk'] as const, errors);
  }
  if (input['seed_k'] !== undefined) ensureInteger('topology.seed_k', input['seed_k'], errors);
  if (input['max_hops'] !== undefined) {
    ensureInteger('topology.max_hops', input['max_hops'], errors);
    if (
      typeof input['max_hops'] === 'number' &&
      Number.isInteger(input['max_hops']) &&
      (input['max_hops'] < 0 || input['max_hops'] > 2)
    ) {
      errors.push('topology.max_hops must be between 0 and 2');
    }
  }
  if (input['hop_decay'] !== undefined) {
    ensureNumber('topology.hop_decay', input['hop_decay'], errors);
    if (typeof input['hop_decay'] === 'number' && (input['hop_decay'] <= 0 || input['hop_decay'] > 1)) {
      errors.push('topology.hop_decay must be greater than 0 and at most 1');
    }
  }
  if (input['include_paths'] !== undefined) {
    ensureBoolean('topology.include_paths', input['include_paths'], errors);
  }

  if (input['edge_policy'] !== undefined) {
    ensureObject('topology.edge_policy', input['edge_policy'], errors);
    const edgePolicy = input['edge_policy'] as Record<string, unknown>;
    const linkTypes = ['supports', 'extends', 'related', 'contradicts', 'supersedes'] as const;
    rejectUnknownKeys('topology.edge_policy', edgePolicy, linkTypes, errors);
    for (const edgeType of linkTypes) {
      const candidate = edgePolicy[edgeType];
      if (candidate === undefined) continue;
      ensureObject(`topology.edge_policy.${edgeType}`, candidate, errors);
      if (candidate && typeof candidate === 'object' && !Array.isArray(candidate)) {
        const typedCandidate = candidate as Record<string, unknown>;
        rejectUnknownKeys(
          `topology.edge_policy.${edgeType}`,
          typedCandidate,
          ['weight', 'direction', 'action'],
          errors
        );
        if (typedCandidate['weight'] !== undefined) {
          ensureNumber(`topology.edge_policy.${edgeType}.weight`, typedCandidate['weight'], errors);
        }
        if (typedCandidate['direction'] !== undefined) {
          ensureEnum(
            `topology.edge_policy.${edgeType}.direction`,
            typedCandidate['direction'],
            ['forward', 'both'] as const,
            errors
          );
        }
        if (typedCandidate['action'] !== undefined) {
          ensureEnum(
            `topology.edge_policy.${edgeType}.action`,
            typedCandidate['action'],
            ['boost', 'flag_conflict', 'shadow_old'] as const,
            errors
          );
        }
      }
    }
  }

  return errors.length ? { ok: false, errors } : { ok: true, value: input as TopologyPolicy };
}

function validateHybridPolicy(input: Record<string, unknown>, errors: string[]): void {
  const hybrid = input['hybrid'];
  if (hybrid === undefined) {
    return;
  }
  if (!hybrid || typeof hybrid !== 'object' || Array.isArray(hybrid)) {
    errors.push('retrieval.hybrid must be object');
    return;
  }

  const hybridRecord = hybrid as Record<string, unknown>;
  rejectUnknownKeys(
    'retrieval.hybrid',
    hybridRecord,
    [
      'alpha',
      'threshold',
      'k_txt',
      'k_vec',
      'k_final',
      'recency_half_life_days',
      'mmr',
      'query_expansion',
      'feedback_boost',
      'topology',
    ],
    errors
  );
  for (const field of ['alpha', 'threshold', 'k_txt', 'k_vec', 'k_final', 'recency_half_life_days']) {
    if (hybridRecord[field] !== undefined) {
      ensureNumber(`retrieval.hybrid.${field}`, hybridRecord[field], errors);
    }
  }

  const objectFields = ['mmr', 'query_expansion', 'feedback_boost', 'topology'];
  for (const field of objectFields) {
    if (
      hybridRecord[field] !== undefined &&
      (!hybridRecord[field] || typeof hybridRecord[field] !== 'object' || Array.isArray(hybridRecord[field]))
    ) {
      errors.push(`retrieval.hybrid.${field} must be object`);
    }
  }

  const topology = hybridRecord['topology'];
  if (topology && typeof topology === 'object') {
    const topologyResult = validateTopologyPolicy(topology as Record<string, unknown>);
    if (!topologyResult.ok) {
      errors.push(...(topologyResult.errors ?? []));
    }
  }
}

export function validateBoundaryPolicy(
  input: Record<string, unknown>
): ValidationResult<BoundaryPolicy> {
  const errors: string[] = [];
  if (!input || typeof input !== 'object' || Array.isArray(input)) {
    return { ok: false, errors: ['boundary must be object'] };
  }
  if (!input['scopes']) errors.push('scopes missing');
  if (!input['boundary_classes']) errors.push('boundary_classes missing');
  if (input['scopes']) {
    const scopes = input['scopes'] as Record<string, Record<string, unknown>>;
    ['session', 'project', 'principle'].forEach((k) => {
      if (!scopes[k]) errors.push(`scopes.${k} missing`);
      else ensureString(`scopes.${k}.ttl`, scopes[k]['ttl'], errors);
    });
  }
  if (input['boundary_classes']) {
    const classes = input['boundary_classes'] as Record<string, Record<string, unknown>>;
    Object.entries(classes).forEach(([cls, v]) => {
      if (!Array.isArray(v['allow'])) errors.push(`boundary_classes.${cls}.allow must be array`);
      if (v['redact'] && !Array.isArray(v['redact']))
        errors.push(`boundary_classes.${cls}.redact must be array`);
    });
  }
  return errors.length
    ? { ok: false, errors }
    : { ok: true, value: input as unknown as BoundaryPolicy };
}

export function validatePolicy(input: Record<string, unknown>): ValidationResult<PolicyDocument> {
  const errors: string[] = [];
  if (!input || typeof input !== 'object' || Array.isArray(input)) {
    return { ok: false, errors: ['policy must be object'] };
  }
  ensureString('version', input['version'], errors);
  if (!input['boundary']) errors.push('boundary missing');
  const boundary = input['boundary'];
  if (!boundary || typeof boundary !== 'object' || Array.isArray(boundary)) {
    errors.push('boundary must be object');
  } else {
    const boundaryResult = validateBoundaryPolicy(boundary as Record<string, unknown>);
    if (!boundaryResult.ok) errors.push(...(boundaryResult.errors ?? []));
  }
  if (input['retrieval'] !== undefined) {
    if (!input['retrieval'] || typeof input['retrieval'] !== 'object' || Array.isArray(input['retrieval'])) {
      errors.push('retrieval must be object');
    } else {
      validateHybridPolicy(input['retrieval'] as Record<string, unknown>, errors);
    }
  }
  if (input['maintenance'] !== undefined) {
    if (!input['maintenance'] || typeof input['maintenance'] !== 'object' || Array.isArray(input['maintenance'])) {
      errors.push('maintenance must be object');
    } else {
      const maint = input['maintenance'] as Record<string, unknown>;
      if (maint['hints_enabled'] !== undefined) {
        ensureBoolean('maintenance.hints_enabled', maint['hints_enabled'], errors);
      }
      if (maint['similarity_threshold'] !== undefined) {
        ensureNumber('maintenance.similarity_threshold', maint['similarity_threshold'], errors);
      }
      if (maint['stale_days'] !== undefined) {
        ensureNumber('maintenance.stale_days', maint['stale_days'], errors);
      }
    }
  }
  return errors.length
    ? { ok: false, errors }
    : { ok: true, value: input as unknown as PolicyDocument };
}

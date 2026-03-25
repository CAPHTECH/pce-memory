import type {
  PolicyDocument,
  BoundaryPolicy,
  ExtractionPolicy,
  ValidationResult,
} from './types.js';

function isString(x: unknown): x is string {
  return typeof x === 'string';
}

function ensureString(field: string, val: unknown, errors: string[]) {
  if (!isString(val)) errors.push(`${field} must be string`);
}

export function validateBoundaryPolicy(input: any): ValidationResult<BoundaryPolicy> {
  const errors: string[] = [];
  if (!input || typeof input !== 'object') {
    return { ok: false, errors: ['boundary must be object'] };
  }
  if (!input.scopes) errors.push('scopes missing');
  if (!input.boundary_classes) errors.push('boundary_classes missing');
  if (input.scopes) {
    ['session', 'project', 'principle'].forEach((k) => {
      if (!input.scopes[k]) errors.push(`scopes.${k} missing`);
      else ensureString(`scopes.${k}.ttl`, input.scopes[k].ttl, errors);
    });
  }
  if (input.boundary_classes) {
    Object.entries(input.boundary_classes).forEach(([cls, v]: any) => {
      if (!Array.isArray(v.allow)) errors.push(`boundary_classes.${cls}.allow must be array`);
      if (v.redact && !Array.isArray(v.redact))
        errors.push(`boundary_classes.${cls}.redact must be array`);
    });
  }
  return errors.length ? { ok: false, errors } : { ok: true, value: input as BoundaryPolicy };
}

export function validatePolicy(input: any): ValidationResult<PolicyDocument> {
  const errors: string[] = [];
  if (!input || typeof input !== 'object') {
    return { ok: false, errors: ['policy must be object'] };
  }
  ensureString('version', input.version, errors);
  if (!input.boundary) errors.push('boundary missing');
  const boundaryResult = validateBoundaryPolicy(input.boundary ?? {});
  if (!boundaryResult.ok) errors.push(...(boundaryResult.errors ?? []));
  if (input.extraction !== undefined) {
    const extractionResult = validateExtractionPolicy(input.extraction);
    if (!extractionResult.ok) {
      errors.push(...(extractionResult.errors ?? []));
    }
  }
  return errors.length ? { ok: false, errors } : { ok: true, value: input as PolicyDocument };
}

export function validateExtractionPolicy(input: any): ValidationResult<ExtractionPolicy> {
  const errors: string[] = [];
  if (!input || typeof input !== 'object') {
    return { ok: false, errors: ['extraction must be object'] };
  }
  if (input.llm_enabled !== undefined && typeof input.llm_enabled !== 'boolean') {
    errors.push('extraction.llm_enabled must be boolean');
  }
  if (input.ollama_endpoint !== undefined) {
    ensureString('extraction.ollama_endpoint', input.ollama_endpoint, errors);
  }
  if (input.model !== undefined) {
    ensureString('extraction.model', input.model, errors);
  }
  return errors.length ? { ok: false, errors } : { ok: true, value: input as ExtractionPolicy };
}

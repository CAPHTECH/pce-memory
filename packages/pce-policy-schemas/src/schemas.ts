import type {
  PolicyDocument,
  BoundaryPolicy,
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
  if (input.maintenance !== undefined) {
    if (!input.maintenance || typeof input.maintenance !== 'object') {
      errors.push('maintenance must be object');
    } else {
      if (input.maintenance.hints_enabled !== undefined) {
        ensureBoolean('maintenance.hints_enabled', input.maintenance.hints_enabled, errors);
      }
      if (input.maintenance.similarity_threshold !== undefined) {
        ensureNumber(
          'maintenance.similarity_threshold',
          input.maintenance.similarity_threshold,
          errors
        );
      }
      if (input.maintenance.stale_days !== undefined) {
        ensureNumber('maintenance.stale_days', input.maintenance.stale_days, errors);
      }
    }
  }
  return errors.length ? { ok: false, errors } : { ok: true, value: input as PolicyDocument };
}

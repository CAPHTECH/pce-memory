import { parse } from 'yaml';
import type { PolicyDocument, ValidationResult } from './types.js';
import { validatePolicy } from './schemas.js';

export function parsePolicy(yamlContent: string): ValidationResult<PolicyDocument> {
  try {
    const parsed = parse(yamlContent);
    return validatePolicy(parsed as Record<string, unknown>);
  } catch (e: unknown) {
    return { ok: false, errors: [`YAML parse error: ${e instanceof Error ? e.message : String(e)}`] };
  }
}

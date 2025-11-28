import { parse } from 'yaml';
import type { PolicyDocument, ValidationResult } from './types.js';
import { validatePolicy } from './schemas.js';

export function parsePolicy(yamlContent: string): ValidationResult<PolicyDocument> {
  try {
    const parsed = parse(yamlContent);
    return validatePolicy(parsed);
  } catch (e: any) {
    return { ok: false, errors: [`YAML parse error: ${e.message ?? String(e)}`] };
  }
}

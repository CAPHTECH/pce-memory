import { parse } from "yaml";
import { PolicyDocument, ValidationResult } from "./types";
import { validatePolicy } from "./schemas";

export function parsePolicy(yamlContent: string): ValidationResult<PolicyDocument> {
  try {
    const parsed = parse(yamlContent);
    return validatePolicy(parsed);
  } catch (e: any) {
    return { ok: false, errors: [`YAML parse error: ${e.message ?? String(e)}`] };
  }
}

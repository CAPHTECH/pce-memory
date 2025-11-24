import { BoundaryPolicy } from "@pce/policy-schemas";

export interface BoundaryValidateInput {
  payload: string;
  allow: string[];
  scope: "session" | "project" | "principle" | string;
}

export interface BoundaryValidateResult {
  allowed: boolean;
  redacted?: string;
  reason?: string;
}

function redact(payload: string, patterns: string[] = []): string {
  let result = payload;
  patterns.forEach((p) => {
    const re = new RegExp(p, "gi");
    result = result.replace(re, "[REDACTED]");
  });
  return result;
}

export function boundaryValidate(
  input: BoundaryValidateInput,
  policy: BoundaryPolicy
): BoundaryValidateResult {
  const { payload, allow, scope } = input;
  const bc = policy.boundary_classes;
  // Simple rule: pick first class that overlaps allow tags
  const matched = Object.values(bc).find((c) => c.allow.some((a) => allow.includes(a) || a === "*"));
  if (!matched) {
    return { allowed: false, reason: "BOUNDARY_DENIED" };
  }
  // Check scope TTL presence as a coarse scope validation
  if (!policy.scopes[scope as keyof typeof policy.scopes]) {
    return { allowed: false, reason: "SCOPE_UNKNOWN" };
  }
  const redacted = matched.redact ? redact(payload, matched.redact) : payload;
  return { allowed: true, redacted };
}

import type { BoundaryPolicy } from '@pce/policy-schemas';

export interface BoundaryValidateInput {
  payload: string;
  allow: string[];
  scope: 'session' | 'project' | 'principle' | string;
}

export interface BoundaryValidateResult {
  allowed: boolean;
  redacted?: string;
  reason?: string;
}

const SAFE_REDACT_PATTERNS: Record<string, RegExp> = {
  email: /\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b/gi,
  phone: /\b\d{2,4}[- ]?\d{2,4}[- ]?\d{3,4}\b/g,
};

export function boundaryValidate(
  input: BoundaryValidateInput,
  policy: BoundaryPolicy
): BoundaryValidateResult {
  const { payload, allow, scope } = input;
  const bc = policy.boundary_classes;
  const matched = Object.values(bc).find((c) =>
    c.allow.some((a) => allow.includes(a) || a === '*')
  );
  if (!matched) {
    return { allowed: false, reason: 'BOUNDARY_DENIED' };
  }
  if (!policy.scopes[scope as keyof typeof policy.scopes]) {
    return { allowed: false, reason: 'SCOPE_UNKNOWN' };
  }
  let redactedPayload = payload;
  if (matched.redact) {
    const patterns = matched.redact
      .map((p) => SAFE_REDACT_PATTERNS[p])
      .filter((re): re is RegExp => re !== undefined);
    redactedPayload = patterns.reduce((acc, re) => acc.replace(re, '[REDACTED]'), payload);
  }
  return { allowed: true, redacted: redactedPayload };
}

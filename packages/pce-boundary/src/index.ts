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

/**
 * allowタグの簡易マッチ（"tool:*" などの末尾ワイルドカードをサポート）
 * handlers.tsでも利用するためexport
 */
export function allowTagMatches(pattern: string, tag: string): boolean {
  if (pattern === '*' || tag === '*') return true;
  if (pattern.endsWith('*')) return tag.startsWith(pattern.slice(0, -1));
  if (tag.endsWith('*')) return pattern.startsWith(tag.slice(0, -1));
  return pattern === tag;
}

/**
 * boundary_class の厳格度マッピング（高いほど厳格）
 * pii/secret は internal/public より厳格なので優先的に選択されるべき
 */
const BOUNDARY_SEVERITY: Record<string, number> = {
  public: 0,
  internal: 1,
  pii: 2,
  secret: 3,
};

export function boundaryValidate(
  input: BoundaryValidateInput,
  policy: BoundaryPolicy
): BoundaryValidateResult {
  const { payload, allow, scope } = input;
  const bc = policy.boundary_classes;
  const classEntries = Object.entries(bc);

  // マッチするすべてのboundary_classを収集（最も厳格なものを選択するため）
  const matchedClasses = classEntries.filter(([, c]) =>
    c.allow.some((a) => allow.some((t) => allowTagMatches(a, t)))
  );

  if (matchedClasses.length === 0) {
    return { allowed: false, reason: 'BOUNDARY_DENIED' };
  }

  // 最も厳格なboundary_classを選択（pii/secret を internal/public より優先）
  // 現在はredactパターンの合成に使用。将来的にはmatchedClassNameを返すAPI拡張も検討
  matchedClasses.sort(([keyA], [keyB]) => {
    const sevA = BOUNDARY_SEVERITY[keyA] ?? 0;
    const sevB = BOUNDARY_SEVERITY[keyB] ?? 0;
    return sevB - sevA; // 降順（厳格なものが先）
  });

  if (!policy.scopes[scope as keyof typeof policy.scopes]) {
    return { allowed: false, reason: 'SCOPE_UNKNOWN' };
  }

  // すべてのマッチしたクラスのredactパターンを合成（PIIもinternalも両方含む場合に漏れないように）
  const allRedactPatterns = new Set<string>();
  for (const [, c] of matchedClasses) {
    if (c.redact) {
      for (const p of c.redact) {
        allRedactPatterns.add(p);
      }
    }
  }

  let redactedPayload = payload;
  if (allRedactPatterns.size > 0) {
    const patterns = Array.from(allRedactPatterns)
      .map((p) => SAFE_REDACT_PATTERNS[p])
      .filter((re): re is RegExp => re !== undefined);
    redactedPayload = patterns.reduce((acc, re) => acc.replace(re, '[REDACTED]'), payload);
  }

  return { allowed: true, redacted: redactedPayload };
}

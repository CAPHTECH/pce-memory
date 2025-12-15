/**
 * テキストの簡易PII/Secret検知とredact
 *
 * 注意:
 * - 完全なPII/Secret検知は不可能（false negative/positiveあり）
 * - 本実装は「誤って保存しない」方向（fail-safe）に寄せた最小実装
 */

export type SensitiveKind =
  | 'email'
  | 'phone'
  | 'credit_card'
  | 'openai_api_key'
  | 'github_token'
  | 'slack_token'
  | 'jwt'
  | 'private_key_block'
  | 'aws_access_key_id';

export interface TextSensitivity {
  pii: SensitiveKind[];
  secret: SensitiveKind[];
}

const PII_DETECT: Array<[SensitiveKind, RegExp]> = [
  ['email', /\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b/i],
  // 電話番号（国際含む・厳密ではない）
  ['phone', /\b\+?\d{1,3}[- ]?\d{2,4}[- ]?\d{2,4}[- ]?\d{3,4}\b/],
  // クレジットカード番号（簡易: 13-19桁、区切りあり）
  ['credit_card', /\b(?:\d[ -]*?){13,19}\b/],
];

const SECRET_DETECT: Array<[SensitiveKind, RegExp]> = [
  ['private_key_block', /-----BEGIN [A-Z0-9 ]*PRIVATE KEY-----/],
  // OpenAI系（例: sk-...）
  ['openai_api_key', /\bsk-[A-Za-z0-9]{20,}\b/],
  // GitHub tokens（例: ghp_..., github_pat_...）
  ['github_token', /\b(?:gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,})\b/],
  // Slack tokens（例: xoxb-...）
  ['slack_token', /\bxox[baprs]-[A-Za-z0-9-]{10,}\b/],
  // JWT（Base64URL 3セグメント）
  ['jwt', /\beyJ[a-zA-Z0-9_-]*\.[a-zA-Z0-9_-]+\.[a-zA-Z0-9_-]+\b/],
  // AWS Access Key ID（秘密そのものではないが強いシグナル）
  ['aws_access_key_id', /\bAKIA[0-9A-Z]{16}\b/],
];

export function analyzeTextSensitivity(text: string): TextSensitivity {
  const pii: SensitiveKind[] = [];
  const secret: SensitiveKind[] = [];

  for (const [kind, re] of PII_DETECT) {
    if (re.test(text)) pii.push(kind);
  }
  for (const [kind, re] of SECRET_DETECT) {
    if (re.test(text)) secret.push(kind);
  }

  return { pii, secret };
}

/**
 * PII向けの簡易redact
 * - Secretは原則として保存しない前提（呼び出し側でdigest-only等にする）
 */
export function redactPiiText(text: string): { redacted: string; hits: SensitiveKind[] } {
  let out = text;
  const hits: SensitiveKind[] = [];

  const replacements: Array<[SensitiveKind, RegExp]> = [
    ['email', /\b[A-Z0-9._%+-]+@[A-Z0-9.-]+\.[A-Z]{2,}\b/gi],
    ['phone', /\b\+?\d{1,3}[- ]?\d{2,4}[- ]?\d{2,4}[- ]?\d{3,4}\b/g],
    ['credit_card', /\b(?:\d[ -]*?){13,19}\b/g],
  ];

  for (const [kind, re] of replacements) {
    if (re.test(out)) {
      hits.push(kind);
      out = out.replace(re, '[REDACTED]');
    }
  }

  return { redacted: out, hits };
}


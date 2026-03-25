/**
 * store/logs.ts のテスト
 * 監査ログDB追記 + ファイル追記のカバレッジ
 */
import { describe, it, expect, beforeEach, afterEach } from 'vitest';
import { mkdtempSync, readFileSync, rmSync, existsSync } from 'fs';
import { join } from 'path';
import { tmpdir } from 'os';
import { initDb, initSchema, resetDbAsync } from '../src/db/connection';
import {
  appendLog,
  appendAuditFile,
  setAuditLogPath,
  recordAudit,
} from '../src/store/logs';

let tempDir: string;

beforeEach(async () => {
  await resetDbAsync();
  process.env.PCE_DB = ':memory:';
  await initDb();
  await initSchema();
  tempDir = mkdtempSync(join(tmpdir(), 'pce-logs-test-'));
});

afterEach(() => {
  setAuditLogPath(undefined);
  if (tempDir && existsSync(tempDir)) {
    rmSync(tempDir, { recursive: true, force: true });
  }
});

describe('appendLog', () => {
  it('inserts audit log entry into DB', async () => {
    await appendLog({
      id: 'log_001',
      op: 'upsert',
      ok: true,
      req: 'req_001',
      trace: 'trace_001',
      policy_version: '1.0',
    });
    // Idempotent: inserting same id again should not throw
    await appendLog({
      id: 'log_001',
      op: 'upsert',
      ok: true,
    });
  });

  it('handles minimal entry (no optional fields)', async () => {
    await appendLog({
      id: 'log_002',
      op: 'activate',
      ok: false,
    });
  });
});

describe('appendAuditFile', () => {
  it('does nothing when auditLogPath is not set', () => {
    setAuditLogPath(undefined);
    // Should not throw
    appendAuditFile({
      request_id: 'req_001',
      trace_id: 'trace_001',
      policy_version: '1.0',
      op: 'upsert',
      ok: true,
    });
  });

  it('writes JSONL record to file', () => {
    const logFile = join(tempDir, 'audit.jsonl');
    setAuditLogPath(logFile);

    appendAuditFile({
      request_id: 'req_001',
      trace_id: 'trace_001',
      policy_version: '1.0',
      op: 'upsert',
      ok: true,
      subject: 'test claim',
    });

    const content = readFileSync(logFile, 'utf-8');
    const lines = content.trim().split('\n');
    expect(lines).toHaveLength(1);

    const record = JSON.parse(lines[0]!);
    expect(record.request_id).toBe('req_001');
    expect(record.op).toBe('upsert');
    expect(record.ok).toBe(true);
    expect(record.subject).toBe('test claim');
    expect(record.ts).toBeDefined();
  });

  it('creates directory if it does not exist', () => {
    const nestedDir = join(tempDir, 'nested', 'dir');
    const logFile = join(nestedDir, 'audit.jsonl');
    setAuditLogPath(logFile);

    appendAuditFile({
      request_id: 'req_002',
      trace_id: 'trace_002',
      policy_version: '1.0',
      op: 'activate',
      ok: true,
    });

    expect(existsSync(logFile)).toBe(true);
  });

  it('appends multiple records', () => {
    const logFile = join(tempDir, 'audit.jsonl');
    setAuditLogPath(logFile);

    appendAuditFile({ request_id: 'r1', trace_id: 't1', policy_version: '1', op: 'a', ok: true });
    appendAuditFile({ request_id: 'r2', trace_id: 't2', policy_version: '1', op: 'b', ok: false });

    const lines = readFileSync(logFile, 'utf-8').trim().split('\n');
    expect(lines).toHaveLength(2);
  });
});

describe('recordAudit', () => {
  it('writes to both DB and file', async () => {
    const logFile = join(tempDir, 'audit.jsonl');
    setAuditLogPath(logFile);

    await recordAudit(
      { id: 'log_003', op: 'feedback', ok: true, req: 'req_003', trace: 'trace_003', policy_version: '1.0' },
      { subject: 'test subject', payload_digest: 'sha256:abc' }
    );

    // File should have the record
    const content = readFileSync(logFile, 'utf-8');
    const record = JSON.parse(content.trim());
    expect(record.op).toBe('feedback');
    expect(record.subject).toBe('test subject');
    expect(record.payload_digest).toBe('sha256:abc');
  });

  it('works without extra fields', async () => {
    await recordAudit({
      id: 'log_004',
      op: 'policy_apply',
      ok: true,
      req: 'req_004',
    });
  });
});

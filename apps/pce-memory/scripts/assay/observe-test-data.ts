/**
 * Observe機能テスト用データ定義
 *
 * goldens/observe.yaml の testCases に対応するテストデータ。
 * run-observe-evaluation.ts から読み込まれる。
 */

export interface ObserveTestCase {
  id: string;
  description: string;
  input: {
    source_type: 'chat' | 'tool' | 'file' | 'http' | 'system';
    source_id?: string;
    content: string;
    boundary_class?: 'public' | 'internal' | 'pii' | 'secret';
    actor?: string;
    tags?: string[];
    provenance?: {
      at: string;
      actor?: string;
      note?: string;
      git?: {
        commit?: string;
        repo?: string;
        url?: string;
        files?: string[];
      };
      url?: string;
      signed?: boolean;
    };
    ttl_days?: number;
    extract?: {
      mode: 'noop' | 'single_claim_v0';
    };
  };
  expected: {
    observation_id_present?: boolean;
    claim_ids_count?: number;
    content_stored?: boolean;
    effective_boundary_class?: 'public' | 'internal' | 'pii' | 'secret';
    content_redacted?: boolean;
    warnings_contains?: string[];
    is_error?: boolean;
    error_code?: string;
    claim_retrievable?: boolean;
    claim_has_evidence?: boolean;
    has_expires_at?: boolean;
  };
}

/**
 * Observeテストケース定義
 */
export const OBSERVE_TEST_CASES: ObserveTestCase[] = [
  // === 基本機能テスト ===
  {
    id: 'obs-001-basic-noop',
    description: '基本的なobserve（extract: noop）',
    input: {
      source_type: 'chat',
      content: 'ユーザーとの会話記録テスト',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      claim_ids_count: 0,
      content_stored: true,
      effective_boundary_class: 'internal',
    },
  },
  {
    id: 'obs-002-basic-extract',
    description: '基本的なobserve（extract: single_claim_v0）',
    input: {
      source_type: 'chat',
      content: '認証にはJWTを使用することに決定',
      extract: { mode: 'single_claim_v0' },
    },
    expected: {
      observation_id_present: true,
      claim_ids_count: 1,
      content_stored: true,
      effective_boundary_class: 'internal',
      claim_retrievable: true,
    },
  },

  // === source_type バリエーション ===
  {
    id: 'obs-003-source-tool',
    description: 'source_type: tool',
    input: {
      source_type: 'tool',
      source_id: 'tool:grep:search_results',
      content: 'grep検索結果: 3件のマッチ',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },
  {
    id: 'obs-004-source-file',
    description: 'source_type: file',
    input: {
      source_type: 'file',
      source_id: 'file:///Users/dev/project/src/main.ts',
      content: '// メインエントリーポイント',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },
  {
    id: 'obs-005-source-http',
    description: 'source_type: http',
    input: {
      source_type: 'http',
      source_id: 'https://api.example.com/v1/users',
      content: '{"users": [{"id": 1, "name": "test"}]}',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },
  {
    id: 'obs-006-source-system',
    description: 'source_type: system',
    input: {
      source_type: 'system',
      content: 'システム起動完了',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },

  // === boundary_class 検知テスト ===
  {
    id: 'obs-010-detect-pii-email',
    description: 'PII検知: メールアドレス',
    input: {
      source_type: 'chat',
      content: '連絡先: user@example.com',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'pii',
      content_stored: true,
      content_redacted: true,
    },
  },
  {
    id: 'obs-011-detect-pii-phone',
    description: 'PII検知: 電話番号',
    input: {
      source_type: 'chat',
      content: '電話番号: 090-1234-5678',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'pii',
      content_stored: true,
      content_redacted: true,
    },
  },
  {
    id: 'obs-012-detect-secret-apikey',
    description: 'Secret検知: APIキー',
    input: {
      source_type: 'chat',
      content: 'sk-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA',
      extract: { mode: 'single_claim_v0' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'secret',
      content_stored: false,
      claim_ids_count: 0,
      warnings_contains: ['OBS_CONTENT_NOT_STORED_SECRET', 'EXTRACT_SKIPPED_SECRET'],
    },
  },
  {
    id: 'obs-013-detect-secret-aws',
    description: 'Secret検知: AWS認証情報',
    input: {
      source_type: 'chat',
      content: 'AKIAIOSFODNN7EXAMPLE',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'secret',
      content_stored: false,
    },
  },

  // === boundary_class 指定テスト ===
  {
    id: 'obs-020-explicit-public',
    description: '明示的なboundary_class: public',
    input: {
      source_type: 'chat',
      content: '公開情報です',
      boundary_class: 'public',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'public',
      content_stored: true,
    },
  },
  {
    id: 'obs-021-explicit-internal',
    description: '明示的なboundary_class: internal',
    input: {
      source_type: 'chat',
      content: '内部情報です',
      boundary_class: 'internal',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      effective_boundary_class: 'internal',
      content_stored: true,
    },
  },

  // === tags テスト ===
  {
    id: 'obs-030-with-tags',
    description: 'tagsを含むobserve',
    input: {
      source_type: 'chat',
      content: 'タグ付きコンテンツ',
      tags: ['project:pce-memory', 'category:design'],
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },
  {
    id: 'obs-031-invalid-tag-chars',
    description: '不正な文字を含むtags（エラー）',
    input: {
      source_type: 'chat',
      content: 'テスト',
      tags: ['valid-tag', 'invalid<script>tag'],
      extract: { mode: 'noop' },
    },
    expected: {
      is_error: true,
      error_code: 'VALIDATION_ERROR',
    },
  },
  {
    id: 'obs-032-tag-too-long',
    description: '長すぎるtags（エラー）',
    input: {
      source_type: 'chat',
      content: 'テスト',
      tags: ['a'.repeat(300)],
      extract: { mode: 'noop' },
    },
    expected: {
      is_error: true,
      error_code: 'VALIDATION_ERROR',
    },
  },

  // === TTL テスト ===
  {
    id: 'obs-040-custom-ttl',
    description: 'カスタムTTL設定',
    input: {
      source_type: 'chat',
      content: '短期保存データ',
      ttl_days: 7,
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
      has_expires_at: true,
    },
  },

  // === actor テスト ===
  {
    id: 'obs-050-with-actor',
    description: 'actorを含むobserve',
    input: {
      source_type: 'chat',
      content: 'アクター指定テスト',
      actor: 'claude-code',
      extract: { mode: 'noop' },
    },
    expected: {
      observation_id_present: true,
      content_stored: true,
    },
  },

  // === provenance テスト ===
  {
    id: 'obs-060-with-provenance',
    description: 'provenanceを含むobserve',
    input: {
      source_type: 'chat',
      content: '出典情報付きデータ',
      provenance: {
        at: '2024-12-16T00:00:00Z',
        actor: 'developer',
        note: 'テスト用データ',
      },
      extract: { mode: 'single_claim_v0' },
    },
    expected: {
      observation_id_present: true,
      claim_ids_count: 1,
      content_stored: true,
    },
  },

  // === extract → activate 統合テスト ===
  {
    id: 'obs-070-extract-activate-flow',
    description: 'observe(extract) → activate フロー',
    input: {
      source_type: 'chat',
      content: 'DuckDBをストレージとして採用',
      extract: { mode: 'single_claim_v0' },
    },
    expected: {
      observation_id_present: true,
      claim_ids_count: 1,
      claim_retrievable: true,
      claim_has_evidence: true,
    },
  },
];

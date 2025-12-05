/**
 * テストデータ定義
 *
 * goldenset評価用のテストclaims。
 * warmupフェーズでupsertされる。
 */

/**
 * テスト用ポリシー
 */
export const TEST_POLICY = {
  version: '1.0.0',
  name: 'test-policy',
  boundary: {
    redact: {
      patterns: [
        {
          name: 'api_key',
          regex: '(?i)(api[_-]?key|apikey)\\s*[:=]\\s*["\']?([a-zA-Z0-9_-]{20,})["\']?',
          replacement: '[REDACTED:API_KEY]',
        },
      ],
    },
  },
};

/**
 * テスト用claims
 *
 * 各カテゴリ（fact, preference, task）のサンプルを含む。
 * IDはgoldenset yamlのexpectedと対応する。
 */
export const TEST_CLAIMS = [
  // === fact (事実・アーキテクチャ決定) ===
  {
    id: 'fact-jwt-auth',
    text: 'JWT認証を採用し、アクセストークンは15分、リフレッシュトークンは7日で有効期限を設定する',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:jwt-auth-001',
    provenance: {
      at: '2024-01-15T10:00:00Z',
      actor: 'architect',
      note: 'ADR-0003: 認証方式の決定',
    },
  },
  {
    id: 'fact-duckdb-storage',
    text: 'DuckDBをローカル永続化ストレージとして使用する。WALモードを有効化し、複数プロセスからの同時アクセスに対応',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:duckdb-storage-001',
    provenance: {
      at: '2024-01-10T09:00:00Z',
      actor: 'architect',
      note: 'ADR-0001: ストレージ選定',
    },
  },
  {
    id: 'fact-fp-ts-error',
    text: 'エラーハンドリングにはfp-tsのEitherを使用し、例外をthrowしない関数型パターンを採用',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:fp-ts-error-001',
    provenance: {
      at: '2024-01-12T14:00:00Z',
      actor: 'lead-dev',
      note: 'コーディング規約: エラーハンドリング',
    },
  },
  {
    id: 'fact-hybrid-search',
    text: 'ハイブリッド検索ではテキスト検索とベクトル検索を組み合わせ、RRF(Reciprocal Rank Fusion)でスコアを融合する',
    kind: 'fact',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:hybrid-search-001',
    provenance: {
      at: '2024-02-01T11:00:00Z',
      actor: 'ml-engineer',
      note: 'ADR-0004: 検索アルゴリズム',
    },
  },

  // === preference (好み・スタイル) ===
  {
    id: 'pref-vitest',
    text: 'テストフレームワークにはVitestを使用する。JestではなくVitestを選択した理由はESM対応とTypeScriptサポートの良さ',
    kind: 'preference',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:vitest-pref-001',
    provenance: {
      at: '2024-01-08T16:00:00Z',
      actor: 'team',
      note: 'ツール選定: テストフレームワーク',
    },
  },
  {
    id: 'pref-handler-prefix',
    text: 'ハンドラ関数にはhandle*プレフィックスを使用する（例: handleUpsert, handleActivate）',
    kind: 'preference',
    scope: 'project',
    boundary_class: 'internal',
    content_hash: 'sha256:handler-prefix-001',
    provenance: {
      at: '2024-01-09T10:00:00Z',
      actor: 'team',
      note: '命名規則: ハンドラ関数',
    },
  },
  {
    id: 'pref-functional-style',
    text: '関数型プログラミングスタイルを好む。mutationを避け、純粋関数を優先する',
    kind: 'preference',
    scope: 'principle',
    boundary_class: 'internal',
    content_hash: 'sha256:functional-style-001',
    provenance: {
      at: '2024-01-05T09:00:00Z',
      actor: 'team',
      note: 'コーディングスタイル',
    },
  },

  // === task (タスク・TODO) ===
  {
    id: 'task-rate-limit',
    text: 'レート制限機能を実装中。トークンバケットアルゴリズムを採用予定',
    kind: 'task',
    scope: 'session',
    boundary_class: 'internal',
    content_hash: 'sha256:rate-limit-task-001',
    provenance: {
      at: '2024-03-01T14:00:00Z',
      actor: 'developer',
      note: 'Sprint 5: レート制限',
    },
  },
  {
    id: 'task-embedding-cache',
    text: '埋め込みキャッシュの最適化が必要。LRUキャッシュの導入を検討中',
    kind: 'task',
    scope: 'session',
    boundary_class: 'internal',
    content_hash: 'sha256:embedding-cache-task-001',
    provenance: {
      at: '2024-03-02T10:00:00Z',
      actor: 'developer',
      note: 'パフォーマンス改善',
    },
  },

  // === policy_hint (ポリシーヒント) ===
  {
    id: 'hint-pii-protection',
    text: 'PIIを含むデータはboundary_class: pii以上で保護する。メールアドレス、電話番号、住所が該当',
    kind: 'policy_hint',
    scope: 'principle',
    boundary_class: 'internal',
    content_hash: 'sha256:pii-hint-001',
    provenance: {
      at: '2024-01-03T09:00:00Z',
      actor: 'security-team',
      note: 'セキュリティポリシー',
    },
  },
];

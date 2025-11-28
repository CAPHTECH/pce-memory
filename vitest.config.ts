import { defineConfig } from 'vitest/config';
import { resolve } from 'path';

export default defineConfig({
  resolve: {
    alias: {
      // ワークスペースパッケージのエイリアス設定
      '@pce/boundary': resolve(__dirname, 'packages/pce-boundary/src/index.ts'),
      '@pce/policy-schemas/src/defaults': resolve(
        __dirname,
        'packages/pce-policy-schemas/src/defaults.ts'
      ),
      '@pce/policy-schemas': resolve(__dirname, 'packages/pce-policy-schemas/src/index.ts'),
      '@pce/embeddings': resolve(__dirname, 'packages/pce-embeddings/src/index.ts'),
      '@pce/sdk-ts': resolve(__dirname, 'packages/pce-sdk-ts/src/index.ts'),
    },
  },
  test: {
    // グローバル設定
    globals: true,
    environment: 'node',

    // CommonJS モジュールの設定
    deps: {
      // native モジュールは外部化
      external: ['@duckdb/node-api', '@duckdb/node-bindings'],
      interopDefault: true,
    },
    // Node.js 環境でのモジュール解決
    server: {
      deps: {
        external: ['@duckdb/node-api', '@duckdb/node-bindings'],
      },
    },

    // カバレッジ設定（LDE要件: 80%以上）
    coverage: {
      provider: 'v8',
      reporter: ['text', 'json', 'html', 'lcov'],
      include: ['packages/*/src/**/*.ts', 'apps/*/src/**/*.ts'],
      exclude: [
        '**/node_modules/**',
        '**/dist/**',
        '**/test/**',
        '**/tests/**',
        '**/*.test.ts',
        '**/*.spec.ts',
        '**/types.ts',
        '**/index.ts',
      ],
      lines: 80,
      functions: 80,
      branches: 80,
      statements: 80,
    },

    // タイムアウト設定（Property-based testは時間がかかる）
    testTimeout: 30000, // 30秒
    hookTimeout: 30000,

    // 並列実行設定
    // テスト間のDuckDB状態分離を確保するためforks poolを使用
    // singleForkでシーケンシャル実行し、フレーキーテストを防止
    pool: 'forks',
    poolOptions: {
      forks: {
        singleFork: true,
        isolate: true,
      },
    },
    // ファイル内のテストも順次実行
    sequence: {
      concurrent: false,
    },

    // レポーター設定
    reporters: ['default', 'json', 'html'],
    outputFile: {
      json: './coverage/test-results.json',
      html: './coverage/test-results.html',
    },

    // Property-based testのフィルタリング
    // `pnpm test:pbt` で Property: プレフィックス付きテストのみ実行
    include: ['**/*.test.ts', '**/*.spec.ts'],
    exclude: ['**/node_modules/**', '**/dist/**'],
  },
});

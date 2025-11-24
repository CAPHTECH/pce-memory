import { defineConfig } from 'vitest/config';

export default defineConfig({
  test: {
    // グローバル設定
    globals: true,
    environment: 'node',

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
    threads: true,
    maxThreads: 4,

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

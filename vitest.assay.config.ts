import { defineConfig } from 'vitest/config';
import { resolve, dirname } from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

export default defineConfig({
  resolve: {
    alias: {
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
    globals: true,
    environment: 'node',
    include: ['apps/pce-memory/scripts/{assay,benchmark}/*.test.ts'],
    testTimeout: 600000,
    hookTimeout: 600000,
    pool: 'forks',
    poolOptions: { forks: { singleFork: true, isolate: true } },
    sequence: { concurrent: false },
    deps: {
      external: ['@duckdb/node-api', '@duckdb/node-bindings'],
      interopDefault: true,
    },
    server: {
      deps: { external: ['@duckdb/node-api', '@duckdb/node-bindings'] },
    },
    reporters: ['default'],
  },
});

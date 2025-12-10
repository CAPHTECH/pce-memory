import { defineConfig } from 'tsdown';

export default defineConfig({
  entry: ['src/index.ts', 'src/daemon/daemon.ts', 'src/client/proxy.ts'],
  format: ['esm'],
  dts: true,
  clean: true,
  // バンドルに含めるパッケージ
  // - fp-ts: ESM互換性問題を回避
  // - @pce/*: workspace依存をバンドル化（npm公開時に単一パッケージ化）
  noExternal: [/^fp-ts/, /^@pce\//],
  // バンドルから除外（npm install時にインストールされる）
  // - @huggingface/transformers: onnxruntime-nodeのネイティブバイナリが必要なため
  external: [/@huggingface\/transformers/],
});

import { defineConfig } from "tsdown";

export default defineConfig({
  entry: ["src/index.ts"],
  format: ["esm"],
  dts: true,
  clean: true,
  // fp-tsをバンドルに含める（ESM互換性問題を回避）
  noExternal: [/^fp-ts/],
});

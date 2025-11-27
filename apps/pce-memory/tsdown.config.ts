import { defineConfig } from "tsdown";

export default defineConfig({
  entry: [
    "src/index.ts",
    "src/daemon/daemon.ts",
    "src/client/proxy.ts",
  ],
  format: ["esm"],
  dts: true,
  clean: true,
  // fp-tsをバンドルに含める（ESM互換性問題を回避）
  // fp-ts/Eitherなどのサブパスインポートも含める
  noExternal: [/^fp-ts/],
});

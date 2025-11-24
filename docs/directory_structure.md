# ディレクトリ／パッケージ構成ガイド（Monorepo 版）

> 本書は **パッケージ境界と役割**にフォーカスして、モノレポ内の構成を明確化する。  
> 既定トランスポートは **stdio**（常駐サーバ不要）。HTTP/WS は任意機能。

---

## 1. ルート構成（リポジトリ名 `pce/`）

```
pce/
├─ apps/                         # 実行物（アプリ/CLI）
│  └─ pce-memory/                # ← MCP サーバ本体（stdio/HTTP両対応）
├─ packages/                     # 共有ライブラリ（publish/内部どちらも可）
│  ├─ pce-sdk-ts/                # TypeScript SDK（クライアント）
│  ├─ pce-boundary/              # 境界検証・redact ユーティリティ
│  ├─ pce-policy-schemas/        # Policy/Boundary/MCP の JSON Schema
│  └─ pce-embeddings/            # Embedding provider アダプタ（OpenAI/Local）
├─ tools/
│  └─ create-pce-memory/         # npx スキャフォルダ（@caphtech/create-pce-memory）
├─ policy/                       # 既定ポリシー（base.yaml）
├─ docs/                         # 仕様・クイックスタート・運用ガイド
├─ .github/workflows/            # CI（差分ビルド/テスト）
├─ package.json                  # ルート scripts（ワークスペース管理のみ）
├─ pnpm-workspace.yaml           # ワークスペース定義（apps/packages/tools）
├─ tsconfig.base.json            # 共通 TS 設定
└─ README.md
```

> **注意**：この文書は**構造の説明**のみ。`package.json` や `ci.yml` の中身は各ファイルを参照。本文に埋め込まない。

---

## 2. パッケージ一覧（役割と公開範囲）

| Directory                     | npm name（例）                    | Type     | Public | 主な役割 |
|---                            |---                                 |---       |---     |---|
| `apps/pce-memory`             | `@caphtech/pce-memory`             | app/bin  | no     | MCP サーバ（stdio/HTTP）。ツール実装・起動 bin（`mcp-stdio`） |
| `packages/pce-sdk-ts`         | `@caphtech/pce-sdk-ts`             | lib      | yes    | TypeScript SDK：クライアントからの activate/search/upsert 等 |
| `packages/pce-boundary`       | `@caphtech/pce-boundary`           | lib      | yes    | 境界検証・redact・前後条件ユーティリティ |
| `packages/pce-policy-schemas` | `@caphtech/pce-policy-schemas`     | lib      | yes    | Policy/Boundary/MCP の JSON Schema（検証） |
| `packages/pce-embeddings`     | `@caphtech/pce-embeddings`         | lib      | yes    | 埋め込みアダプタ（OpenAI/Local の切替） |
| `tools/create-pce-memory`     | `@caphtech/create-pce-memory`      | tool     | yes    | npx スキャフォルダ（雛形生成、stdio 既定） |

> **Public** 列は npm publish 可否の初期想定。実運用に合わせて private でも良い。

---

## 3. 依存関係の方針（内部）

- `apps/pce-memory` は **SDK 以外の packages すべて**を利用可：  
  `pce-boundary`, `pce-policy-schemas`, `pce-embeddings`
- `pce-sdk-ts` は **純クライアント**。サーバ内部実装へ依存しない。
- `create-pce-memory` は **SDK + スキーマ**に依存可。サーバ本体には依存しない（雛形生成のみ）。

依存の例（擬似）：
```
apps/pce-memory
 ├─ packages/pce-boundary
 ├─ packages/pce-policy-schemas
 └─ packages/pce-embeddings
packages/pce-sdk-ts
 └─ packages/pce-policy-schemas
tools/create-pce-memory
 ├─ packages/pce-sdk-ts
 └─ packages/pce-policy-schemas
```

---

## 4. 各パッケージのファイル構成（雛形）

### 4.1 apps/pce-memory
```
apps/pce-memory/
├─ src/
│  ├─ index.ts                # transport 切替（stdio 既定）
│  ├─ mcp/stdio.ts            # stdio transport 実装
│  ├─ mcp/tools/*.ts          # activate/search/upsert/feedback/validate/policy.apply
│  ├─ core/*                  # extractor/integrator/retriever/critic/boundary/policy
│  └─ store/sqlite/schema.sql # DDL（claims/entities/relations/...）
├─ bin/
│  ├─ mcp-stdio               # #!/usr/bin/env node（npx エントリ）
│  └─ pce-memory              # HTTP/WS 起動（任意）
├─ policy/base.yaml
├─ package.json               # "bin", "start:stdio", "start:http"
└─ README.md
```

### 4.2 packages/pce-sdk-ts
```
packages/pce-sdk-ts/
├─ src/index.ts               # Client: activate/search/upsert/feedback/validate
├─ package.json               # "main", "types"
└─ README.md
```

### 4.3 packages/pce-boundary
```
packages/pce-boundary/
├─ src/index.ts               # validate(), redact(), precedence(), pre/post
├─ package.json
└─ README.md
```

### 4.4 packages/pce-policy-schemas
```
packages/pce-policy-schemas/
├─ src/policy.schema.json
├─ src/mcp-tools.schema.json
├─ package.json
└─ README.md
```

### 4.5 packages/pce-embeddings
```
packages/pce-embeddings/
├─ src/openai.ts              # OpenAI adapter
├─ src/local.ts               # Local embedding
├─ src/index.ts               # provider factory
├─ package.json
└─ README.md
```

### 4.6 tools/create-pce-memory
```
tools/create-pce-memory/
├─ bin/create-pce-memory      # #!/usr/bin/env node
├─ template/                  # apps/pce-memory 雛形（stdio 既定）
├─ package.json
└─ README.md
```

---

## 5. ルートワークスペース（参照のみ）

- `pnpm-workspace.yaml`：  
  ```yaml
  packages:
    - "apps/*"
    - "packages/*"
    - "tools/*"
  ```
- ルート `package.json`：ワークスペース管理スクリプトのみ（publish しない）
- `tsconfig.base.json`：`@pce/*` で packages をインポート

> ファイル中身は各ファイルを参照。**本ドキュメントに貼り付けない**。

---

## 6. スクリプトと開発

- `pnpm dev` … 既定で `apps/pce-memory` の **stdio 起動**  
- `pnpm dev:http` … HTTP/WS 起動（任意）  
- `pnpm -r build / test / lint` … ワークスペース一括

---

## 7. 命名規則・公開

- npm スコープは例として `@caphtech/` を使用。組織スコープに合わせて変更可。
- 破壊変更は各パッケージの **SemVer** に従う（changesets 推奨）。

---

## 8. よくある混乱と回答

- **「apps と packages の違い？」**  
  実行可能物（サーバ/CLI）は *apps*、再利用可能なライブラリは *packages*。
- **「SDK はサーバに依存する？」**  
  しない。SDK はクライアント向け API と型だけ提供（MCP/HTTP 問わず）。
- **「HTTP を使わない場合？」**  
  既定は **stdio**。HTTP/WS は `apps/pce-memory/bin/pce-memory` を任意で使う。

---

## 9. 参考ドキュメント

- Quickstart: `docs/mcp_quickstart.md`  
- MCP Tools Spec: `docs/mcp-tools.md`  
- Boundary/Policy: `docs/boundary-policy.md`  
- Vision/Model: `docs/pce-memory-vision.ja.md`, `docs/pce-model.ja.md`, `docs/pce.md`

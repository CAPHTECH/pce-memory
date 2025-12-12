# Git Hooks Integration

PCE-Memoryの知識をGitリポジトリと自動同期するためのガイド。

## 概要

Git hooksを使用して、コミット前にローカルDBから`.pce-shared/`へエクスポートし、マージ後に`.pce-shared/`からローカルDBへインポートする。これにより、チームメンバー間でプロジェクトの知識を共有できる。

### 同期フロー

```
                   ┌─────────────┐
                   │   開発者A   │
                   └──────┬──────┘
                          │
    [pre-commit]          │         [post-merge]
    ローカルDB ──push──> .pce-shared/ <──pull── ローカルDB
                          │
                          ↓
                   ┌─────────────┐
                   │    Git      │
                   └──────┬──────┘
                          │
                          ↓
                   ┌─────────────┐
                   │   開発者B   │
                   └─────────────┘
```

## クイックスタート

### 1. Hooksのインストール

```bash
# リポジトリのルートディレクトリで実行
./scripts/git-hooks/install-hooks.sh

# シンボリックリンクを使用する場合
./scripts/git-hooks/install-hooks.sh --symlink

# 既存のフックを上書きする場合
./scripts/git-hooks/install-hooks.sh --force
```

### 2. 同期の有効化

環境変数で同期を有効化:

```bash
# 一時的に有効化
export PCE_SYNC_ENABLED=true

# 永続的に有効化（~/.zshrc または ~/.bashrc に追加）
echo 'export PCE_SYNC_ENABLED=true' >> ~/.zshrc
```

### 3. 動作確認

```bash
# 現在のステータスを確認
pce-memory sync status

# 手動でpush
pce-memory sync push

# 手動でpull（dry-run）
pce-memory sync pull --dry-run
```

## 設定オプション

### 環境変数

| 変数名                     | デフォルト    | 説明                                        |
| -------------------------- | ------------- | ------------------------------------------- |
| `PCE_SYNC_ENABLED`         | `false`       | `true`で同期を有効化                        |
| `PCE_SYNC_TARGET_DIR`      | `.pce-shared` | pushのエクスポート先                        |
| `PCE_SYNC_SOURCE_DIR`      | `.pce-shared` | pullのインポート元                          |
| `PCE_SYNC_SCOPE_FILTER`    | -             | スコープフィルタ（例: `project,principle`） |
| `PCE_SYNC_BOUNDARY_FILTER` | -             | 境界クラスフィルタ（例: `public,internal`） |
| `PCE_SYNC_AUTO_STAGE`      | `true`        | push後に自動で`git add`                     |
| `PCE_SYNC_DRY_RUN`         | `false`       | pullをdry-runモードで実行                   |
| `PCE_SYNC_QUIET`           | `false`       | ログ出力を抑制                              |

### 推奨設定

チーム共有用の設定例:

```bash
# プロジェクト固有の知識のみを共有
export PCE_SYNC_ENABLED=true
export PCE_SYNC_SCOPE_FILTER=project,principle

# 内部情報は共有しない
export PCE_SYNC_BOUNDARY_FILTER=public
```

開発環境用の設定例:

```bash
# すべてのスコープを同期
export PCE_SYNC_ENABLED=true

# PIIとsecretは除外（デフォルト動作）
```

## CLIコマンド

### sync push

ローカルDBから`.pce-shared/`へエクスポート:

```bash
pce-memory sync push [options]

Options:
  --target-dir <path>      エクスポート先（デフォルト: .pce-shared）
  --scope-filter <scopes>  スコープフィルタ（カンマ区切り）
  --boundary-filter <bc>   境界クラスフィルタ（カンマ区切り）
  --since <ISO8601>        指定日時以降の変更のみ
```

例:

```bash
# デフォルト設定でpush
pce-memory sync push

# プロジェクトと原則のみ
pce-memory sync push --scope-filter project,principle

# 過去1週間の変更のみ
pce-memory sync push --since 2025-01-01T00:00:00Z
```

### sync pull

`.pce-shared/`からローカルDBへインポート:

```bash
pce-memory sync pull [options]

Options:
  --source-dir <path>      インポート元（デフォルト: .pce-shared）
  --scope-filter <scopes>  スコープフィルタ（カンマ区切り）
  --boundary-filter <bc>   境界クラスフィルタ（カンマ区切り）
  --dry-run                変更をプレビューのみ
  --since <ISO8601>        指定日時以降の変更のみ
```

例:

```bash
# デフォルト設定でpull
pce-memory sync pull

# dry-runでプレビュー
pce-memory sync pull --dry-run

# 公開情報のみインポート
pce-memory sync pull --boundary-filter public
```

### sync status

同期ディレクトリの状態を確認:

```bash
pce-memory sync status [options]

Options:
  --target-dir <path>      確認対象（デフォルト: .pce-shared）
```

出力例:

```
[pce-sync] Sync directory: /path/to/project/.pce-shared
  Exists: yes
  Files:
    - Claims: 42
    - Entities: 15
    - Relations: 23
  Manifest:
    - Version: 1.0.0
    - PCE Memory Version: 0.6.0
    - Last Push: 2025-01-10T10:30:00.000Z
    - Last Pull: 2025-01-10T09:15:00.000Z
```

## CRDT同期戦略

### マージルール

PCE-Memoryは**G-Set CRDT（Grow-only Set）**をベースにした同期戦略を採用:

1. **冪等性**: 同じデータを複数回インポートしても結果は同一
2. **可換性**: インポート順序に依存しない
3. **結合律**: `(A merge B) merge C = A merge (B merge C)`

### 境界クラスの単調性

境界クラスは厳格度が上がる方向にのみマージ:

```
public(0) < internal(1) < pii(2) < secret(3)
```

例:

- ローカル: `public` + リモート: `internal` → 結果: `internal`
- ローカル: `pii` + リモート: `public` → 結果: `pii`（変更なし）

### 衝突検出

以下の場合に衝突が検出される:

| タイプ                  | 説明                 | 解決方法                     |
| ----------------------- | -------------------- | ---------------------------- |
| `boundary_upgrade`      | 境界クラスの格上げ   | 自動解決（格上げを適用）     |
| `entity_content_diff`   | 同一IDで内容が異なる | スキップ（既存を維持）       |
| `relation_content_diff` | 同一IDで内容が異なる | スキップ（既存を維持）       |
| `missing_reference`     | 参照先が存在しない   | スキップ（インポートしない） |

衝突情報は`sync pull`の出力で確認可能:

```
[pce-sync] Imported: 10 claims (new), 5 entities, 8 relations
[pce-sync] Conflicts:
  - Auto-resolved: 2
  - Skipped: 1
  - [boundary_upgrade] Claim clm_abc123: boundary upgraded from public to internal
```

## .gitignore設定

`.pce-shared/`をリポジトリに含めるため、`.gitignore`に追加しない:

```gitignore
# PCE-Memory local DB (DO NOT commit)
*.pce.db
*.pce.db.wal
*.pce.db.lock

# PCE-Memory shared directory (DO commit)
# !.pce-shared/
```

## トラブルシューティング

### hooksが実行されない

1. 実行権限を確認:

```bash
ls -la .git/hooks/
# pre-commit と post-merge に実行権限があるか確認
```

2. `PCE_SYNC_ENABLED`が設定されているか確認:

```bash
echo $PCE_SYNC_ENABLED
```

### pce-memoryコマンドが見つからない

```bash
# グローバルインストール
npm install -g pce-memory

# または npx を使用
npx pce-memory sync status
```

### 衝突が多発する

同じIDを持つ異なる内容のエンティティが存在する可能性。canonical_keyを使用してデータを一意に識別:

```json
{
  "id": "ent_xxx",
  "canonical_key": "user:john.doe@example.com",
  "type": "Actor",
  "name": "John Doe"
}
```

### dry-runで変更を確認

本番前にdry-runで確認:

```bash
pce-memory sync pull --dry-run
```

## セキュリティ考慮事項

### 境界クラスの適切な設定

- `secret`クラスのデータは**同期されない**（デフォルト動作）
- `pii`クラスは慎重に扱う
- チーム共有時は`--boundary-filter public,internal`を推奨

### 機密情報の除外

APIキーやパスワードは絶対にClaimに保存しない:

```typescript
// NG: 機密情報をClaimに保存
await upsert({
  text: 'API_KEY=sk-xxxxx',
  boundary_class: 'secret', // 同期されないが、ローカルDBに残る
});

// OK: 環境変数の名前のみ記録
await upsert({
  text: '認証にはAPI_KEY環境変数を使用',
  boundary_class: 'internal',
});
```

## Hooksのアンインストール

```bash
./scripts/git-hooks/install-hooks.sh --uninstall
```

または手動で削除:

```bash
rm .git/hooks/pre-commit
rm .git/hooks/post-merge
```

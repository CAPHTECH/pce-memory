---
name: pce-sync
context: fork
description: "pce-memoryのチーム間知識同期スキル。push/pull/statusを管理し、Git hooks連携とCRDTマージを支援する。「sync knowledge」「push knowledge」「pull team knowledge」「check sync status」「知識を同期」「同期状態を確認」と言われた時に使用する。"
argument-hint: "[push|pull|status]"
allowed-tools: "mcp__pce-memory__pce_memory_sync_push, mcp__pce-memory__pce_memory_sync_pull, mcp__pce-memory__pce_memory_sync_status, mcp__pce-memory__pce_memory_state"
---

# PCE Sync - Team Knowledge Synchronization

pce-memoryの知識をチーム間で同期する。Git hooks連携とCRDT（G-Set）ベースのマージを提供。

## 引数の解釈

`$ARGUMENTS` を解析する:
- `push` → ローカル知識をエクスポート
- `pull` → チーム知識をインポート
- `status` → 同期状態の確認
- 引数なし → status を実行してガイド

## 操作

### Push（エクスポート）

ローカルDBの知識を `.pce-shared/` ディレクトリにエクスポートする。

```
pce_memory_sync_push()
```

- エクスポート先: `$PCE_SYNC_TARGET_DIR`（デフォルト: `.pce-shared/`）
- `PCE_SYNC_AUTO_STAGE=true` の場合、自動で `git add` される
- scope フィルタ: `PCE_SYNC_SCOPE_FILTER` で制限可能

### Pull（インポート）

`.pce-shared/` からチームの知識をインポートする。

```
pce_memory_sync_pull()
// または dry-run で確認
pce_memory_sync_pull({ dry_run: true })
```

- CRDT（G-Set）ベースのマージ: 追加のみ、削除なし
- Boundary昇格: `public < internal < pii < secret`（上方向のみ）
- コンフリクト: boundary_upgrade は自動解決、entity/relation差分はスキップ

### Status（状態確認）

```
pce_memory_sync_status()
```

返される情報:
- ローカルとリモートのclaim数
- 未同期のclaim数
- 最終同期日時
- コンフリクトの有無

## Git Hooks 連携

### セットアップ

```bash
# hooks のインストール
./scripts/git-hooks/install-hooks.sh

# 環境変数の設定
export PCE_SYNC_ENABLED=true
```

### 動作フロー

```
git commit → pre-commit hook → sync push（自動エクスポート）
git pull   → post-merge hook → sync pull（自動インポート）
```

## CRDT マージ戦略

[crdt-merge-guide.md](references/crdt-merge-guide.md) を参照。

## トラブルシューティング

- **sync push が失敗する**: `pce_memory_state` で状態を確認。Ready 状態でないと push できない
- **pull でコンフリクト**: boundary_upgrade は自動解決。entity/relation の差分は手動確認
- **大量の未同期**: `sync status` で確認し、`sync push` → `git commit` → `git push`

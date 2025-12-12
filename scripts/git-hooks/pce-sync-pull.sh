#!/bin/bash
# pce-sync-pull.sh - post-merge hook for PCE-Memory sync
#
# Git merge/pull後に自動的に.pce-shared/からローカルDBにインポートする
#
# Usage:
#   - .git/hooks/post-merge にシンボリックリンクまたはコピー
#   - または install-hooks.sh を使用
#
# Environment Variables:
#   PCE_SYNC_ENABLED     - "true" で有効化（デフォルト: false）
#   PCE_SYNC_SOURCE_DIR  - インポート元ディレクトリ（デフォルト: .pce-shared）
#   PCE_SYNC_DRY_RUN     - "true" でdry-runモード（デフォルト: false）
#   PCE_SYNC_QUIET       - "true" で出力抑制（デフォルト: false）
#
# Exit Codes:
#   0 - 成功（またはスキップ）
#   1 - エラー（commit/mergeは失敗しない）

set -euo pipefail

# 設定
PCE_SYNC_ENABLED="${PCE_SYNC_ENABLED:-false}"
PCE_SYNC_SOURCE_DIR="${PCE_SYNC_SOURCE_DIR:-.pce-shared}"
PCE_SYNC_DRY_RUN="${PCE_SYNC_DRY_RUN:-false}"
PCE_SYNC_QUIET="${PCE_SYNC_QUIET:-false}"

log() {
  if [ "$PCE_SYNC_QUIET" != "true" ]; then
    echo "[pce-sync] $*" >&2
  fi
}

warn() {
  echo "[pce-sync] WARNING: $*" >&2
}

error() {
  echo "[pce-sync] ERROR: $*" >&2
}

# 有効化チェック
if [ "$PCE_SYNC_ENABLED" != "true" ]; then
  exit 0
fi

# 同期ディレクトリの存在チェック
if [ ! -d "$PCE_SYNC_SOURCE_DIR" ]; then
  log "Sync directory not found: $PCE_SYNC_SOURCE_DIR (skipping pull)"
  exit 0
fi

# pce-memory コマンドの存在チェック
if ! command -v pce-memory &> /dev/null; then
  warn "pce-memory command not found. Install with: npm install -g pce-memory"
  exit 0
fi

log "Starting sync pull from $PCE_SYNC_SOURCE_DIR..."

# Pull実行
ARGS=(sync pull --source-dir "$PCE_SYNC_SOURCE_DIR")

if [ "$PCE_SYNC_DRY_RUN" = "true" ]; then
  ARGS+=(--dry-run)
fi

if pce-memory "${ARGS[@]}"; then
  log "Sync pull completed successfully"
else
  error "Sync pull failed (continuing anyway)"
fi

exit 0

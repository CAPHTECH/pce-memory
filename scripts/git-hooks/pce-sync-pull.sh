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
#   PCE_SYNC_SOURCE_DIR  - インポート元ディレクトリ（未指定時: <git_root>/.pce-shared）
#   PCE_SYNC_DRY_RUN     - "true" でdry-runモード（デフォルト: false）
#   PCE_SYNC_QUIET       - "true" で出力抑制（デフォルト: false）
#
# Exit Codes:
#   0 - 成功（またはスキップ）
#   1 - エラー（commit/mergeは失敗しない）

set -euo pipefail

# 設定
PCE_SYNC_ENABLED="${PCE_SYNC_ENABLED:-false}"
PCE_SYNC_SOURCE_DIR="${PCE_SYNC_SOURCE_DIR:-}"
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

# git hooks は必ずリポジトリルートで実行する（サブディレクトリ起動の揺れを防ぐ）
if git_root="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  if ! cd "$git_root"; then
    warn "Failed to cd to git root: $git_root (continuing in $(pwd))"
  fi
fi

SOURCE_DIR_EFFECTIVE="$PCE_SYNC_SOURCE_DIR"
if [ -z "$SOURCE_DIR_EFFECTIVE" ]; then
  SOURCE_DIR_EFFECTIVE=".pce-shared"
fi

# 同期ディレクトリの存在チェック
if [ ! -d "$SOURCE_DIR_EFFECTIVE" ]; then
  log "Sync directory not found: $SOURCE_DIR_EFFECTIVE (skipping pull)"
  exit 0
fi

# pce-memory コマンドの存在チェック
if ! command -v pce-memory &> /dev/null; then
  warn "pce-memory command not found. Install with: npm install -g pce-memory"
  exit 0
fi

log "Starting sync pull from $SOURCE_DIR_EFFECTIVE..."

# Pull実行
ARGS=(sync pull)
if [ -n "$PCE_SYNC_SOURCE_DIR" ]; then
  ARGS+=(--source-dir "$PCE_SYNC_SOURCE_DIR")
fi

if [ "$PCE_SYNC_DRY_RUN" = "true" ]; then
  ARGS+=(--dry-run)
fi

if pce-memory "${ARGS[@]}"; then
  log "Sync pull completed successfully"
else
  error "Sync pull failed (continuing anyway)"
fi

exit 0

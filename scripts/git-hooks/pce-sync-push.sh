#!/bin/bash
# pce-sync-push.sh - pre-commit hook for PCE-Memory sync
#
# Git commit前に自動的にローカルDBから.pce-shared/へエクスポートする
#
# Usage:
#   - .git/hooks/pre-commit にシンボリックリンクまたはコピー
#   - または install-hooks.sh を使用
#
# Environment Variables:
#   PCE_SYNC_ENABLED       - "true" で有効化（デフォルト: false）
#   PCE_SYNC_TARGET_DIR    - エクスポート先ディレクトリ（未指定時: <git_root>/.pce-shared）
#   PCE_SYNC_SCOPE_FILTER  - スコープフィルタ（カンマ区切り、例: project,principle）
#   PCE_SYNC_BOUNDARY_FILTER - 境界クラスフィルタ（例: public,internal）
#   PCE_SYNC_QUIET         - "true" で出力抑制（デフォルト: false）
#   PCE_SYNC_AUTO_STAGE    - "true" で自動的にgit addする（デフォルト: true）
#
# Exit Codes:
#   0 - 成功（commitを続行）
#   1 - エラー（commitを中断）

set -euo pipefail

# 設定
PCE_SYNC_ENABLED="${PCE_SYNC_ENABLED:-false}"
PCE_SYNC_TARGET_DIR="${PCE_SYNC_TARGET_DIR:-}"
PCE_SYNC_SCOPE_FILTER="${PCE_SYNC_SCOPE_FILTER:-}"
PCE_SYNC_BOUNDARY_FILTER="${PCE_SYNC_BOUNDARY_FILTER:-}"
PCE_SYNC_QUIET="${PCE_SYNC_QUIET:-false}"
PCE_SYNC_AUTO_STAGE="${PCE_SYNC_AUTO_STAGE:-true}"

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

# pce-memory コマンドの存在チェック
if ! command -v pce-memory &> /dev/null; then
  warn "pce-memory command not found. Install with: npm install -g pce-memory"
  exit 0
fi

# git hooks は必ずリポジトリルートで実行する（サブディレクトリ起動の揺れを防ぐ）
if git_root="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  if ! cd "$git_root"; then
    warn "Failed to cd to git root: $git_root (continuing in $(pwd))"
  fi
fi

TARGET_DIR_EFFECTIVE="$PCE_SYNC_TARGET_DIR"
if [ -z "$TARGET_DIR_EFFECTIVE" ]; then
  TARGET_DIR_EFFECTIVE=".pce-shared"
fi

log "Starting sync push to $TARGET_DIR_EFFECTIVE..."

# Push実行
ARGS=(sync push)
if [ -n "$PCE_SYNC_TARGET_DIR" ]; then
  ARGS+=(--target-dir "$PCE_SYNC_TARGET_DIR")
fi

if [ -n "$PCE_SYNC_SCOPE_FILTER" ]; then
  ARGS+=(--scope-filter "$PCE_SYNC_SCOPE_FILTER")
fi

if [ -n "$PCE_SYNC_BOUNDARY_FILTER" ]; then
  ARGS+=(--boundary-filter "$PCE_SYNC_BOUNDARY_FILTER")
fi

if pce-memory "${ARGS[@]}"; then
  log "Sync push completed successfully"

  # 自動ステージング
  if [ "$PCE_SYNC_AUTO_STAGE" = "true" ] && [ -d "$TARGET_DIR_EFFECTIVE" ]; then
    # 変更があるかチェック
    if ! git diff --quiet "$TARGET_DIR_EFFECTIVE" 2>/dev/null || \
       [ -n "$(git ls-files --others --exclude-standard "$TARGET_DIR_EFFECTIVE" 2>/dev/null)" ]; then
      log "Staging changes in $TARGET_DIR_EFFECTIVE..."
      git add "$TARGET_DIR_EFFECTIVE"
    fi
  fi
else
  error "Sync push failed"
  exit 1
fi

exit 0

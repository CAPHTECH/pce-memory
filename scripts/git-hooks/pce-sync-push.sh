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
#   PCE_SYNC_TARGET_DIR    - エクスポート先ディレクトリ（デフォルト: .pce-shared）
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
PCE_SYNC_TARGET_DIR="${PCE_SYNC_TARGET_DIR:-.pce-shared}"
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

log "Starting sync push to $PCE_SYNC_TARGET_DIR..."

# Push実行
ARGS=(sync push --target-dir "$PCE_SYNC_TARGET_DIR")

if [ -n "$PCE_SYNC_SCOPE_FILTER" ]; then
  ARGS+=(--scope-filter "$PCE_SYNC_SCOPE_FILTER")
fi

if [ -n "$PCE_SYNC_BOUNDARY_FILTER" ]; then
  ARGS+=(--boundary-filter "$PCE_SYNC_BOUNDARY_FILTER")
fi

if pce-memory "${ARGS[@]}"; then
  log "Sync push completed successfully"

  # 自動ステージング
  if [ "$PCE_SYNC_AUTO_STAGE" = "true" ] && [ -d "$PCE_SYNC_TARGET_DIR" ]; then
    # 変更があるかチェック
    if ! git diff --quiet "$PCE_SYNC_TARGET_DIR" 2>/dev/null || \
       [ -n "$(git ls-files --others --exclude-standard "$PCE_SYNC_TARGET_DIR" 2>/dev/null)" ]; then
      log "Staging changes in $PCE_SYNC_TARGET_DIR..."
      git add "$PCE_SYNC_TARGET_DIR"
    fi
  fi
else
  error "Sync push failed"
  exit 1
fi

exit 0

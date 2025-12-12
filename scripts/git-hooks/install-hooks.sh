#!/bin/bash
# install-hooks.sh - PCE-Memory Git hooks installer
#
# プロジェクトの .git/hooks にPCE-Memory同期用フックをインストールする
#
# Usage:
#   ./install-hooks.sh [options]
#
# Options:
#   --uninstall    フックを削除
#   --symlink      コピーではなくシンボリックリンクを作成
#   --force        既存のフックを上書き
#   --help         ヘルプを表示
#
# インストールされるフック:
#   - pre-commit: pce-sync-push.sh
#   - post-merge: pce-sync-pull.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
HOOKS_DIR=""
USE_SYMLINK=false
FORCE=false
UNINSTALL=false

# 色付き出力
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log_info() {
  echo -e "${GREEN}[INFO]${NC} $*"
}

log_warn() {
  echo -e "${YELLOW}[WARN]${NC} $*"
}

log_error() {
  echo -e "${RED}[ERROR]${NC} $*" >&2
}

show_help() {
  cat << EOF
PCE-Memory Git Hooks Installer

Usage: $0 [options]

Options:
  --uninstall    Remove installed hooks
  --symlink      Create symlinks instead of copying
  --force        Overwrite existing hooks
  --help         Show this help message

This script installs the following hooks:
  - pre-commit: Exports local DB to .pce-shared/ before commit
  - post-merge: Imports from .pce-shared/ after merge/pull

After installation, enable sync by setting environment variable:
  export PCE_SYNC_ENABLED=true

Or add to your shell profile (~/.bashrc, ~/.zshrc):
  echo 'export PCE_SYNC_ENABLED=true' >> ~/.zshrc
EOF
}

find_git_hooks_dir() {
  # git rev-parse で .git ディレクトリを取得
  local git_dir
  if git_dir=$(git rev-parse --git-dir 2>/dev/null); then
    HOOKS_DIR="${git_dir}/hooks"
    return 0
  else
    log_error "Not in a git repository"
    return 1
  fi
}

install_hook() {
  local source="$1"
  local target="$2"
  local hook_name="$3"

  if [ ! -f "$source" ]; then
    log_error "Source file not found: $source"
    return 1
  fi

  if [ -e "$target" ]; then
    if [ "$FORCE" = true ]; then
      log_warn "Overwriting existing $hook_name hook"
      rm -f "$target"
    else
      # 既存のフックがPCE-Memoryのものかチェック
      if grep -q "pce-sync" "$target" 2>/dev/null; then
        log_info "$hook_name hook already installed (use --force to reinstall)"
        return 0
      else
        log_warn "$hook_name hook already exists. Use --force to overwrite."
        log_warn "Or manually add the hook to your existing $hook_name script."
        return 0
      fi
    fi
  fi

  if [ "$USE_SYMLINK" = true ]; then
    ln -s "$source" "$target"
    log_info "Created symlink: $target -> $source"
  else
    cp "$source" "$target"
    chmod +x "$target"
    log_info "Installed $hook_name hook"
  fi
}

uninstall_hook() {
  local target="$1"
  local hook_name="$2"

  if [ -e "$target" ]; then
    # PCE-Memoryのフックかチェック
    if grep -q "pce-sync" "$target" 2>/dev/null || [ -L "$target" ]; then
      rm -f "$target"
      log_info "Removed $hook_name hook"
    else
      log_warn "$hook_name hook is not a PCE-Memory hook. Skipping removal."
    fi
  else
    log_info "$hook_name hook not found. Nothing to remove."
  fi
}

# 引数パース
while [[ $# -gt 0 ]]; do
  case $1 in
    --uninstall)
      UNINSTALL=true
      shift
      ;;
    --symlink)
      USE_SYMLINK=true
      shift
      ;;
    --force)
      FORCE=true
      shift
      ;;
    --help|-h)
      show_help
      exit 0
      ;;
    *)
      log_error "Unknown option: $1"
      show_help
      exit 1
      ;;
  esac
done

# Gitリポジトリのチェック
if ! find_git_hooks_dir; then
  exit 1
fi

# hooksディレクトリの作成
mkdir -p "$HOOKS_DIR"

# アンインストール
if [ "$UNINSTALL" = true ]; then
  log_info "Uninstalling PCE-Memory hooks..."
  uninstall_hook "$HOOKS_DIR/pre-commit" "pre-commit"
  uninstall_hook "$HOOKS_DIR/post-merge" "post-merge"
  log_info "Uninstallation complete"
  exit 0
fi

# インストール
log_info "Installing PCE-Memory hooks to $HOOKS_DIR..."

install_hook "$SCRIPT_DIR/pce-sync-push.sh" "$HOOKS_DIR/pre-commit" "pre-commit"
install_hook "$SCRIPT_DIR/pce-sync-pull.sh" "$HOOKS_DIR/post-merge" "post-merge"

log_info "Installation complete!"
echo ""
log_info "To enable sync, set environment variable:"
echo "  export PCE_SYNC_ENABLED=true"
echo ""
log_info "Optional configuration:"
echo "  # (unset) uses <git_root>/.pce-shared"
echo "  PCE_SYNC_TARGET_DIR=.pce-shared     # Export directory override"
echo "  PCE_SYNC_SOURCE_DIR=.pce-shared     # Import directory override"
echo "  PCE_SYNC_SCOPE_FILTER=project,principle"
echo "  PCE_SYNC_AUTO_STAGE=true            # Auto git add"

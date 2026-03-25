#!/bin/bash
# MCP server launcher with per-project DB path resolution
# Used by .mcp.json to ensure PCE_DB is set before the server starts

if [ -z "$PCE_DB" ]; then
  # Resolve project name from CWD (git-aware, worktree-safe)
  ABS_COMMON_DIR=$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
  if [ -n "$ABS_COMMON_DIR" ]; then
    PROJECT_NAME=$(basename "$(dirname "$ABS_COMMON_DIR")")
  else
    PROJECT_NAME=$(basename "$PWD")
  fi
  DB_DIR="$HOME/.pce/projects/$PROJECT_NAME"
  mkdir -p "$DB_DIR"
  export PCE_DB="$DB_DIR/memory.db"
fi

exec npx pce-memory@latest

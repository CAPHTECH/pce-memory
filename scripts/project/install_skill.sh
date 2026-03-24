#!/usr/bin/env bash

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"
SOURCE_DIR="${REPO_ROOT}/.claude/skills/pce-memory-project-manager"
TARGET_DIR="${HOME}/.codex/skills/pce-memory-project-manager"

mkdir -p "$(dirname "${TARGET_DIR}")"
rm -rf "${TARGET_DIR}"
ln -s "${SOURCE_DIR}" "${TARGET_DIR}"

echo "installed skill symlink:"
echo "  ${TARGET_DIR} -> ${SOURCE_DIR}"

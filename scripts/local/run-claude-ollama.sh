#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
MODEL="${LOCAL_VALIDATION_MODEL:-qwen3.5:122b-a10b}"

fail() {
  echo "[local-validation] $*" >&2
  exit 1
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    fail "missing required command: $1"
  fi
}

require_cmd claude
require_cmd ollama

[[ -d "$ROOT" ]] || fail "repository root not found: $ROOT"
[[ -n "$MODEL" ]] || fail "LOCAL_VALIDATION_MODEL must not be empty"

if ! ollama show "$MODEL" >/dev/null 2>&1; then
  cat >&2 <<EOF
[local-validation] Ollama model '$MODEL' is not ready.

Expected preflight:
  ollama serve
  ollama pull $MODEL
  ollama show $MODEL
EOF
  exit 1
fi

cd "$ROOT"
if [[ $# -eq 0 ]]; then
  exec ollama launch claude --model "$MODEL"
fi

exec ollama launch claude --model "$MODEL" -- "$@"

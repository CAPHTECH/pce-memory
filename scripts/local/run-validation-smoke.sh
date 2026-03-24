#!/usr/bin/env bash
set -euo pipefail
umask 077

SCRIPT_DIR=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
OUTPUT_ROOT="${LOCAL_VALIDATION_OUTPUT_ROOT:-$ROOT/validation/local}"
MODEL="${LOCAL_VALIDATION_MODEL:-qwen3.5:122b-a10b}"
TASK_ID="memory-architecture-smoke"
TASK_FILE="$ROOT/validation/tasks/${TASK_ID}.md"
AGENT="codex"
PREPARE_ONLY=false
RUN_ID=""
KEEP_RUN_DIR=false
RUN_PARENT_DIR=""
RUN_DIR=""

fail() {
  echo "[local-validation] $*" >&2
  exit 1
}

usage() {
  cat <<'EOF'
Usage: scripts/local/run-validation-smoke.sh [--agent codex|claude] [--prepare-only] [--run-id <id>]
EOF
}

require_cmd() {
  if ! command -v "$1" >/dev/null 2>&1; then
    fail "missing required command: $1"
  fi
}

assert_not_symlink() {
  local path="$1"
  if [[ -L "$path" ]]; then
    fail "path must not be a symlink: $path"
  fi
}

# shellcheck disable=SC2329
cleanup() {
  local exit_code=$?
  trap - EXIT INT TERM HUP

  if [[ "$KEEP_RUN_DIR" != true && -n "$RUN_DIR" && -d "$RUN_DIR" ]]; then
    rm -rf -- "$RUN_DIR"
  fi

  if [[ "$KEEP_RUN_DIR" != true && -n "$RUN_PARENT_DIR" ]]; then
    rmdir "$RUN_PARENT_DIR" 2>/dev/null || true
  fi

  exit "$exit_code"
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --agent)
      [[ $# -ge 2 ]] || fail "--agent requires a value"
      AGENT="${2:-}"
      shift 2
      ;;
    --prepare-only)
      PREPARE_ONLY=true
      shift
      ;;
    --run-id)
      [[ $# -ge 2 ]] || fail "--run-id requires a value"
      RUN_ID="${2:-}"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "[local-validation] unknown argument: $1" >&2
      usage >&2
      exit 1
      ;;
  esac
done

case "$AGENT" in
  codex|claude)
    ;;
  *)
    fail "--agent must be codex or claude"
    ;;
esac

require_cmd ollama
require_cmd node

[[ -d "$ROOT" ]] || fail "repository root not found: $ROOT"
[[ -f "$TASK_FILE" ]] || fail "task file not found: $TASK_FILE"
[[ -n "$MODEL" ]] || fail "LOCAL_VALIDATION_MODEL must not be empty"

if [[ "$OUTPUT_ROOT" != /* ]]; then
  OUTPUT_ROOT="$ROOT/$OUTPUT_ROOT"
fi

RUN_DATE=$(date +%F)
if [[ -z "$RUN_ID" ]]; then
  RUN_ID="${AGENT}-$(date +%H%M%S)-$$"
fi

[[ "$RUN_ID" =~ ^[A-Za-z0-9._-]+$ ]] || fail "run-id must match ^[A-Za-z0-9._-]+$"

if [[ "$AGENT" == "codex" ]]; then
  require_cmd codex
else
  require_cmd claude
fi

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

RUN_DIR="$OUTPUT_ROOT/$RUN_DATE/$RUN_ID"
SUMMARY_FILE="$RUN_DIR/summary.md"
META_FILE="$RUN_DIR/meta.json"
LOG_FILE="$RUN_DIR/run.log"
PROMPT_FILE="$RUN_DIR/prompt.md"
RUN_PARENT_DIR="$OUTPUT_ROOT/$RUN_DATE"

trap cleanup EXIT INT TERM HUP
if [[ -e "$OUTPUT_ROOT" && ! -d "$OUTPUT_ROOT" ]]; then
  fail "output root is not a directory: $OUTPUT_ROOT"
fi
assert_not_symlink "$OUTPUT_ROOT"
mkdir -p -- "$RUN_PARENT_DIR"
if [[ -e "$RUN_PARENT_DIR" && ! -d "$RUN_PARENT_DIR" ]]; then
  fail "run parent directory is not a directory: $RUN_PARENT_DIR"
fi
assert_not_symlink "$OUTPUT_ROOT"
assert_not_symlink "$RUN_PARENT_DIR"
mkdir -- "$RUN_DIR" || fail "run directory already exists: $RUN_DIR"
cp "$TASK_FILE" "$PROMPT_FILE"

OLLAMA_VERSION=$(ollama --version 2>&1 | tail -n 1 | tr -d '\r')
START_TS=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
START_EPOCH=$(date +%s)

write_meta() {
  local status="$1"
  local success="$2"
  local runtime="$3"
  local notes="$4"

  META_AGENT="$AGENT" \
  META_LOG_PATH="run.log" \
  META_MODEL="$MODEL" \
  META_NOTES="$notes" \
  META_OLLAMA_VERSION="$OLLAMA_VERSION" \
  META_PROMPT_PATH="prompt.md" \
  META_RUN_DATE="$RUN_DATE" \
  META_RUN_ID="$RUN_ID" \
  META_RUNTIME="$runtime" \
  META_STARTED_AT="$START_TS" \
  META_STATUS="$status" \
  META_SUCCESS="$success" \
  META_SUMMARY_PATH="summary.md" \
  META_TASK_ID="$TASK_ID" \
  node <<'EOF' > "$META_FILE"
const data = {
  agent: process.env.META_AGENT,
  model: process.env.META_MODEL,
  ollama_version: process.env.META_OLLAMA_VERSION,
  task_id: process.env.META_TASK_ID,
  run_id: process.env.META_RUN_ID,
  run_date: process.env.META_RUN_DATE,
  started_at: process.env.META_STARTED_AT,
  runtime_seconds: Number(process.env.META_RUNTIME),
  success: process.env.META_SUCCESS === 'true',
  status: process.env.META_STATUS,
  summary_path: process.env.META_SUMMARY_PATH,
  prompt_path: process.env.META_PROMPT_PATH,
  log_path: process.env.META_LOG_PATH,
  notes: process.env.META_NOTES,
};

process.stdout.write(`${JSON.stringify(data, null, 2)}\n`);
EOF
}

write_meta "prepared" false 0 "Run prepared but not executed yet."

if [[ "$PREPARE_ONLY" == true ]]; then
  echo "[local-validation] prepared smoke run at $RUN_DIR"
  exit 0
fi

STATUS="failure"
SUCCESS=false
NOTES="Agent run failed. Inspect run.log for details."
COMMAND_SUCCEEDED=false

if [[ "$AGENT" == "codex" ]]; then
  if "$ROOT/scripts/local/run-codex-ollama.sh" exec --sandbox read-only -o "$SUMMARY_FILE" - <"$PROMPT_FILE" >"$LOG_FILE" 2>&1; then
    COMMAND_SUCCEEDED=true
  fi
else
  if "$ROOT/scripts/local/run-claude-ollama.sh" -p --output-format text "$(cat "$PROMPT_FILE")" >"$SUMMARY_FILE" 2>"$LOG_FILE"; then
    COMMAND_SUCCEEDED=true
    if [[ -s "$SUMMARY_FILE" ]]; then
      printf '%s\n' '--- summary stdout ---' >>"$LOG_FILE"
      cat "$SUMMARY_FILE" >>"$LOG_FILE"
    fi
  fi
fi

if [[ "$COMMAND_SUCCEEDED" == true && -s "$SUMMARY_FILE" ]]; then
  STATUS="success"
  SUCCESS=true
  if [[ "$AGENT" == "codex" ]]; then
    NOTES="Codex smoke run completed."
  else
    STATUS="success"
    SUCCESS=true
    NOTES="Claude Code smoke run completed."
  fi
elif [[ "$COMMAND_SUCCEEDED" == true ]]; then
  NOTES="Agent command exited successfully but did not produce a non-empty summary."
fi

END_EPOCH=$(date +%s)
RUNTIME=$((END_EPOCH - START_EPOCH))

if [[ "$SUCCESS" != true ]]; then
  if [[ -s "$SUMMARY_FILE" ]]; then
    printf '%s\n' '--- partial summary before failure fallback ---' >>"$LOG_FILE"
    cat "$SUMMARY_FILE" >>"$LOG_FILE"
  fi
  cat > "$SUMMARY_FILE" <<EOF
# Smoke Run Failed

The local validation smoke run did not complete successfully.

- agent: \`$AGENT\`
- model: \`$MODEL\`
- run_id: \`$RUN_ID\`

Inspect \`run.log\` for the full stderr/stdout trace.
EOF
fi

write_meta "$STATUS" "$SUCCESS" "$RUNTIME" "$NOTES"
KEEP_RUN_DIR=true
echo "[local-validation] $STATUS: $RUN_DIR"

if [[ "$SUCCESS" == true ]]; then
  exit 0
fi

exit 1

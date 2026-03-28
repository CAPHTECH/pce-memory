#!/bin/bash
# Stop hook: Instruct Claude to persist session context before ending.
# Detects runtime via stdin JSON (Claude Code provides stop_hook_active field).
# Claude Code: uses stop_hook_active for loop guard + decision:block output.
# Cursor: uses lock file for loop guard + followup_message output.

# Read stdin JSON (may be empty for Cursor)
INPUT=$(cat 2>/dev/null || echo '{}')

# Detect runtime: Claude Code provides stop_hook_active in stdin JSON
IS_CLAUDE_CODE=false
if echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); sys.exit(0 if 'stop_hook_active' in d else 1)" 2>/dev/null; then
  IS_CLAUDE_CODE=true
fi

# Loop guard: prevent infinite re-triggers
if [ "$IS_CLAUDE_CODE" = "true" ]; then
  # Claude Code: use stop_hook_active field from stdin
  STOP_ACTIVE=$(echo "$INPUT" | python3 -c "import sys,json; print(json.load(sys.stdin).get('stop_hook_active', False))" 2>/dev/null)
  if [ "$STOP_ACTIVE" = "True" ]; then
    echo '{}'
    exit 0
  fi
else
  # Cursor: use lock file for loop guard (created after successful output below)
  # Use session-unique key: CURSOR_TRANSCRIPT_PATH (per-session) > CLAUDE_PROJECT_DIR (per-project)
  CURSOR_SESSION_KEY=$(echo "${CURSOR_TRANSCRIPT_PATH:-${CLAUDE_PROJECT_DIR:-${PWD}}}" | shasum -a 256 | cut -c1-16)
  CURSOR_LOCK_FILE="/tmp/pce-memory-stop-hook-cursor-${CURSOR_SESSION_KEY}"
  if [ -f "$CURSOR_LOCK_FILE" ]; then
    # TTL: ignore lock files older than 60 seconds (covers stop cycle, not legitimate re-stops)
    if [ "$(find "$CURSOR_LOCK_FILE" -mmin -1 2>/dev/null)" ]; then
      echo '{}'
      exit 0
    else
      rm -f "$CURSOR_LOCK_FILE"
    fi
  fi
fi

INSTRUCTIONS='Session ending. Persist important context using the v2 workflow. Step 1 - Close completed tasks: For any task claims (kind: task) recalled via activate that are now done, send pce_memory_feedback(claim_id, signal: completed). Step 2 - Record incomplete task state (PRIORITY if work is in progress): Call pce_memory_upsert with kind=task, scope=project, boundary_class=internal, memory_type=working_state, provenance with current ISO timestamp. Text format: TASK [status:in_progress|blocked] description. Progress: what was done. Next: next steps. Blockers: blockers or none. Always write in English. Step 3 - Promote durable discoveries: For confirmed project- or principle-level contracts (invariants, recovery rules, search semantics, migration constraints, runbook steps): prefer pce_memory_observe then pce_memory_distill then pce_memory_promote. Use pce_memory_upsert only for already-distilled knowledge with provenance. Include entities and relations when graph structure is obvious. Use pce_memory_link_claims to connect related claims (supports/extends/contradicts/related). Never upsert scope: session or boundary_class: secret. Skip this step for minor fixes or obvious info. Step 4 - Send feedback: pce_memory_feedback only for durable claim_id values that were activated and actually used in this session (helpful/outdated/harmful/duplicate/completed). Step 5 - Graph maintenance (optional, only if many claims were added): Run pce_memory_graph_audit to check for orphans, contradiction cycles, or scope holes. Address critical findings before ending. After completing all steps, allow the session to end.'

if [ "$IS_CLAUDE_CODE" = "true" ]; then
  # Claude Code CLI: use decision:block format
  python3 -c "
import json, sys
instructions = sys.stdin.read()
print(json.dumps({'decision': 'block', 'reason': instructions}))
" <<< "$INSTRUCTIONS"
else
  # Cursor: use followup_message format
  OUTPUT=$(python3 -c "
import json, sys
instructions = sys.stdin.read()
print(json.dumps({'followup_message': instructions}))
" <<< "$INSTRUCTIONS")
  if [ $? -eq 0 ] && [ -n "$OUTPUT" ]; then
    echo "$OUTPUT"
    touch "$CURSOR_LOCK_FILE"
  else
    # JSON generation failed; output empty to avoid corrupted response
    echo '{}'
  fi
fi

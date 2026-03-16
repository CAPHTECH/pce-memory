#!/bin/bash
# SessionStart hook: Fires on startup AND after compact.
# Sets per-project DB path and determines appropriate action.

INPUT=$(cat)

# Extract fields using python3 for robust JSON parsing
SOURCE=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('source',''))" 2>/dev/null || true)
CWD=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('cwd',''))" 2>/dev/null || true)

# Set per-project DB path via CLAUDE_ENV_FILE (only on startup, not compact)
if [ "$SOURCE" != "compact" ] && [ -n "$CLAUDE_ENV_FILE" ] && [ -n "$CWD" ]; then
  # Create project-specific DB directory
  PROJECT_NAME=$(basename "$CWD")
  DB_DIR="$HOME/.pce/projects/$PROJECT_NAME"
  mkdir -p "$DB_DIR"
  echo "export PCE_DB=\"$DB_DIR/memory.db\"" >> "$CLAUDE_ENV_FILE"
fi

TASK_RECOVERY_INSTRUCTION="Run pce_memory_activate (q: 'TASK status in_progress blocked next steps', scope: [project], allow: [\"answer:task\"], top_k: 5) to recover task state. From results, IGNORE claims with low confidence (< 0.5) or that contain '[status:done]' - these are completed tasks. Only treat claims containing '[status:in_progress]' or '[status:blocked]' as active work."

if [ "$SOURCE" = "compact" ]; then
  CONTEXT="Context compaction occurred. Previously activated knowledge is lost. Immediately: 1. Run pce_memory_activate (q: keywords of the current task, scope: [project, principle], allow: [\"answer:task\", \"answer:fact\"], top_k: 10) to re-retrieve relevant knowledge. 2. $TASK_RECOVERY_INSTRUCTION Use results internally without reporting to the user."
else
  CONTEXT="pce-memory session start (execute now): 1. Check state with pce_memory_state 2. If Uninitialized, run pce_memory_policy_apply 3. Run pce_memory_activate (q: current project/directory name, scope: [project, principle], allow: [\"answer:task\", \"answer:fact\"], top_k: 10) 4. $TASK_RECOVERY_INSTRUCTION If active tasks found, report to user. 5. Use other results internally without reporting to the user."
fi

python3 -c "
import json, sys
print(json.dumps({
    'hookSpecificOutput': {
        'hookEventName': 'SessionStart',
        'additionalContext': sys.argv[1]
    }
}))
" "$CONTEXT"

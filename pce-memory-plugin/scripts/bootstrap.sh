#!/bin/bash
# SessionStart hook: Fires on startup AND after compact.
# Sets per-project DB path and injects the activate-first workflow.

INPUT=$(cat)

# Extract fields using python3 for robust JSON parsing
SOURCE=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('source',''))" 2>/dev/null || true)
CWD=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('cwd',''))" 2>/dev/null || true)

# Set per-project DB path via CLAUDE_ENV_FILE (only on startup, not compact)
if [ "$SOURCE" != "compact" ] && [ -n "$CLAUDE_ENV_FILE" ] && [ -n "$CWD" ]; then
  # Create project-specific DB directory (shared across worktrees)
  # Resolve absolute git-common-dir to ensure worktrees share the same DB
  ABS_COMMON_DIR=$(cd "$CWD" && git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
  if [ -n "$ABS_COMMON_DIR" ]; then
    # Use main repo's toplevel directory name (works for both main repo and worktrees)
    # For worktrees: common-dir points to main repo's .git, so dirname gives main repo root
    # For main repo: common-dir == git-dir, dirname also gives repo root
    PROJECT_NAME=$(basename "$(dirname "$ABS_COMMON_DIR")")
  else
    # Non-git directory: use CWD basename
    PROJECT_NAME=$(basename "$CWD")
  fi
  DB_DIR="$HOME/.pce/projects/$PROJECT_NAME"
  mkdir -p "$DB_DIR"
  echo "export PCE_DB=\"$DB_DIR/memory.db\"" >> "$CLAUDE_ENV_FILE"
fi

TASK_RECOVERY_INSTRUCTION="If state is HasClaims or Ready, run pce_memory_activate (q: 'task status in progress blocked next steps', scope: [project], allow: [\"answer:task\"], top_k: 5) to recover task state. Ignore claims with low confidence or completed-task markers. Only treat '[status:in_progress]' and '[status:blocked]' as active work."

if [ "$SOURCE" = "compact" ]; then
  CONTEXT="Context compaction occurred. Previously activated knowledge is lost. Immediately: 1. Check pce_memory_state. 2. If state is HasClaims or Ready, run pce_memory_activate (q: English keywords of the current task, scope: [project, principle], allow: [\"answer:task\"], top_k: 10) to re-retrieve relevant knowledge. 3. $TASK_RECOVERY_INSTRUCTION Use results internally unless they reveal an active task the user should know about."
else
  CONTEXT="pce-memory session start (execute now): 1. Check state with pce_memory_state. 2. If state is Uninitialized, run pce_memory_policy_apply. 3. If state is HasClaims or Ready, run pce_memory_activate (q: English keywords for the current project and task, scope: [project, principle], allow: [\"answer:task\"], top_k: 10). 4. $TASK_RECOVERY_INSTRUCTION 5. If active tasks are found, report them briefly to the user. Use other recalled knowledge internally without reporting it."
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

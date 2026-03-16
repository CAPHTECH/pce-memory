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

if [ "$SOURCE" = "compact" ]; then
  CONTEXT="Context compaction occurred. Previously activated knowledge is lost. Immediately run pce_memory_activate to re-retrieve relevant knowledge (q: keywords of the current task, scope: project/principle, top_k: 10). Use results internally without reporting to the user."
else
  CONTEXT="pce-memory session start (execute now): 1. Check state with pce_memory_state 2. If Uninitialized, run pce_memory_policy_apply (scope: session/project/principle, boundary: public/internal) 3. Run pce_memory_activate (q: current project/directory name, scope: project/principle, top_k: 10) 4. Use results internally without reporting to the user."
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

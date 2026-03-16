#!/bin/bash
# SessionStart hook: Fires on startup AND after compact.
# Uses the "source" field to determine appropriate action.

INPUT=$(cat)

# Extract source field (startup, resume, clear, compact)
SOURCE=$(echo "$INPUT" | sed -n 's/.*"source"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

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

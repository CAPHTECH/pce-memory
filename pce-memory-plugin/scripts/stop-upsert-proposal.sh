#!/bin/bash
# Stop hook: Auto-record important decisions before session ends
cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "Stop",
    "additionalContext": "Before ending, record important decisions/discoveries from this session with pce_memory_upsert:\n- Architecture/design decisions (kind: fact)\n- New coding conventions/patterns (kind: preference)\n- Bug root causes and fixes (kind: fact)\n- Incomplete task state (kind: task)\n\nSkip if nothing significant (minor fixes, already-known info only).\nSend pce_memory_feedback for any recalled knowledge that was used."
  }
}
EOF

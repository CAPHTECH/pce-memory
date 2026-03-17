#!/bin/bash
# UserPromptSubmit hook: Inject the conservative pce-memory protocol on every user message.
# Task-like prompts get an additional activate instruction.

INPUT=$(cat)

# Extract the user prompt text using python3 for robust JSON parsing
PROMPT=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('userPrompt',''))" 2>/dev/null || true)

# Base protocol (always injected)
BASE="pce-memory autonomous operation: Before the first non-state pce_memory call in this turn, check pce_memory_state. State guard: Uninitialized -> run pce_memory_policy_apply; PolicyApplied -> upsert allowed but skip activate/feedback; HasClaims -> upsert/activate allowed but skip feedback; Ready -> all tools allowed. Use pce_memory_activate as the primary recall path. Record only durable knowledge with pce_memory_upsert: architecture decisions, API/schema decisions, technical constraints, naming/tooling conventions, bug root causes, and in-progress/blocked task state. Do NOT record minor fixes, obvious repo facts, speculative notes, completed tasks as new task claims, or secrets. When recording task state, use: 'TASK [status:in_progress|blocked] <description>. Progress: <...>. Next: <...>. Blockers: <...>.' Send pce_memory_feedback only for recalled knowledge that actually affected the work. After context compaction, re-run pce_memory_activate when prior recalled knowledge is no longer present. Always write upsert text and activate queries in English."

# Task detection
if echo "$PROMPT" | grep -qiE '(implement|add|create|build|fix|bug|error|design|refactor|debug|investigate|migrate|delete|remove|change|update|modify|test|review|deploy|configure|setup|install|upgrade)'; then
  ACTIVATE=" Task detected: follow the state guard; if state is HasClaims or Ready, run pce_memory_activate before starting work (extract English keywords from the user prompt for q, scope: [project, principle], allow: [\"answer:task\"], use results internally unless they reveal active task state that the user should know about)."
else
  ACTIVATE=""
fi

# Use python for safe JSON encoding to avoid escaping issues
python3 -c "
import json, sys
ctx = sys.argv[1] + sys.argv[2]
print(json.dumps({
    'hookSpecificOutput': {
        'hookEventName': 'UserPromptSubmit',
        'additionalContext': ctx
    }
}))
" "$BASE" "$ACTIVATE"

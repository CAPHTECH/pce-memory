#!/bin/bash
# UserPromptSubmit hook: Inject pce-memory protocol on every user message.
# Task-like prompts get an additional activate instruction.

INPUT=$(cat)

# Extract the user prompt text using python3 for robust JSON parsing
PROMPT=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('userPrompt',''))" 2>/dev/null || true)

# Base protocol (always injected)
BASE="pce-memory autonomous operation: Before the first non-state pce_memory call in this turn, check pce_memory_state. State guard: Uninitialized → run pce_memory_policy_apply; PolicyApplied → upsert allowed but skip activate/feedback; HasClaims → upsert/activate allowed but skip feedback; Ready → all tools allowed. Record important design decisions with pce_memory_upsert. Send pce_memory_feedback when recalled knowledge was helpful/outdated (Ready state only). Record: architecture decisions, technical constraints, API specs, naming conventions, bug root causes. Do NOT record: minor fixes, obvious info, secrets. After context compaction, re-retrieve knowledge with pce_memory_activate if previously activated knowledge is no longer in conversation. Always write upsert text and activate queries in English for consistent embedding search and team sync."

# Task detection
if echo "$PROMPT" | grep -qiE '(implement|add|create|build|fix|bug|error|design|refactor|debug|investigate|migrate|delete|remove|change|update|modify|test|review|deploy|configure|setup|install|upgrade)'; then
  ACTIVATE=" Task detected: follow the state guard; if state is HasClaims or Ready, run pce_memory_activate before starting work (extract keywords from user prompt for q, scope: project/principle, use results internally only)."
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

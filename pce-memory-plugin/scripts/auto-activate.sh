#!/bin/bash
# UserPromptSubmit hook: Inject pce-memory protocol on every user message.
# Task-like prompts get an additional activate instruction.

INPUT=$(cat)

# Extract the user prompt text (portable - no grep -P on macOS)
PROMPT=$(echo "$INPUT" | sed -n 's/.*"userPrompt"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

# Base protocol (always injected)
BASE="pce-memory autonomous operation: Record important design decisions with pce_memory_upsert. Send pce_memory_feedback when recalled knowledge was helpful/outdated. Record: architecture decisions, technical constraints, API specs, naming conventions, bug root causes. Do NOT record: minor fixes, obvious info, secrets. After context compaction, re-retrieve knowledge with pce_memory_activate if previously activated knowledge is no longer in conversation."

# Task detection (Japanese + English)
if echo "$PROMPT" | grep -qiE '(実装|追加|作成|修正|バグ|エラー|設計|リファクタ|implement|add|create|fix|bug|error|design|refactor|debug|investigate|調査|移行|削除|変更|更新|テスト|test|review|レビュー)'; then
  ACTIVATE=" Task detected: Run pce_memory_activate before starting work (extract keywords from user prompt for q, scope: project/principle, use results internally only)."
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

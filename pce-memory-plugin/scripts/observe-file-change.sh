#!/bin/bash
# PostToolUse (Write|Edit) hook: Auto-observe significant file changes (v2)

INPUT=$(cat)

# Extract the file path using python3 for robust JSON parsing
FILE_PATH=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('tool_input',{}).get('file_path',''))" 2>/dev/null || true)

SHOULD_OBSERVE=false

# Detect architecturally significant file changes (narrowed patterns)
if echo "$FILE_PATH" | grep -qiE '(schema\.|migration|/api/|/routes?/|middleware|/auth/|\.env(\.|$)|docker-compose|Dockerfile)'; then
  SHOULD_OBSERVE=true
fi

if [ "$SHOULD_OBSERVE" = true ]; then
  cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "PostToolUse",
    "additionalContext": "Architecturally significant file changed. If this change involves a design decision worth preserving: (1) Use pce_memory_observe to capture the raw change context as scratchpad. (2) If the decision is confirmed and reusable, prefer observe → distill → promote in the same task. Use pce_memory_upsert only for already-distilled knowledge. For speculative or in-progress changes, observe only — do not promote until the decision is validated. Keep scope: session for transient findings."
  }
}
EOF
else
  echo '{}'
fi

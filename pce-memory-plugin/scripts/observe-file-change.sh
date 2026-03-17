#!/bin/bash
# PostToolUse (Write|Edit) hook: Auto-observe significant file changes

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
    "additionalContext": "Architecturally significant file changed. Treat this as a recording candidate only. Record it with pce_memory_upsert only if the change made an explicit and durable decision or constraint. API contracts, schema decisions, config decisions, auth decisions, and bug root causes may be recorded. Do not record speculative or minor implementation detail."
  }
}
EOF
else
  echo '{}'
fi

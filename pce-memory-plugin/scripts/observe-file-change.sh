#!/bin/bash
# PostToolUse (Write|Edit) hook: Auto-observe significant file changes

INPUT=$(cat)

# Extract the file path from tool input (portable - no grep -P on macOS)
FILE_PATH=$(echo "$INPUT" | sed -n 's/.*"file_path"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

SHOULD_OBSERVE=false

# Detect architecturally significant file changes
if echo "$FILE_PATH" | grep -qiE '(config|schema|migration|api|route|middleware|auth|index\.(ts|js)|package\.json|tsconfig|\.env)'; then
  SHOULD_OBSERVE=true
fi

if [ "$SHOULD_OBSERVE" = true ]; then
  cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "PostToolUse",
    "additionalContext": "Architecturally significant file changed. If this change involves a design decision, record it with pce_memory_upsert. API contracts, schema changes, config changes, and auth changes should be recorded. Update entities/relations as needed."
  }
}
EOF
else
  echo '{}'
fi

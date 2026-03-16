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
    "additionalContext": "アーキテクチャ上重要なファイルが変更された。この変更が設計決定を含む場合は pce_memory_upsert で記録すること。API契約・スキーマ・設定・認証の変更は記録対象。エンティティやリレーションの更新も必要に応じて実行する。"
  }
}
EOF
else
  echo '{}'
fi

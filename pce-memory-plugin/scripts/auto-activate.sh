#!/bin/bash
# UserPromptSubmit hook: Auto-activate for new tasks
#
# Detects task-like patterns and instructs AI to activate automatically.

INPUT=$(cat)

# Extract the user prompt text (portable - no grep -P on macOS)
PROMPT=$(echo "$INPUT" | sed -n 's/.*"userPrompt"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

# Detect patterns that benefit from knowledge activation
SHOULD_ACTIVATE=false

# Task start patterns (Japanese + English)
if echo "$PROMPT" | grep -qiE '(実装|追加|作成|修正|バグ|エラー|設計|リファクタ|implement|add|create|fix|bug|error|design|refactor|debug|investigate|調査|移行|削除|変更|更新|テスト|test|review|レビュー)'; then
  SHOULD_ACTIVATE=true
fi

if [ "$SHOULD_ACTIVATE" = true ]; then
  cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "UserPromptSubmit",
    "additionalContext": "新しいタスクを検出。作業開始前に pce_memory_activate を実行してから作業に入ること。ユーザーのプロンプトからキーワードを抽出し q に設定する。scope は [\"project\", \"principle\"]。結果はユーザーに報告せず内部的に参照する。"
  }
}
EOF
else
  echo '{}'
fi

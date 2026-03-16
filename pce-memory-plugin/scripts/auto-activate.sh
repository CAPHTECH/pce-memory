#!/bin/bash
# UserPromptSubmit hook: Inject pce-memory protocol on every user message.
# Task-like prompts get an additional activate instruction.

INPUT=$(cat)

# Extract the user prompt text (portable - no grep -P on macOS)
PROMPT=$(echo "$INPUT" | sed -n 's/.*"userPrompt"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

# Base protocol (always injected)
BASE="pce-memory自律運用: 重要な設計決定をしたら pce_memory_upsert で記録する。想起した知識が役立った/古かった場合は pce_memory_feedback を送る。記録対象: アーキテクチャ決定、技術的制約、API仕様、命名規則、バグの根本原因。記録しない: 軽微な修正、自明な情報、secret。"

# Task detection (Japanese + English)
if echo "$PROMPT" | grep -qiE '(実装|追加|作成|修正|バグ|エラー|設計|リファクタ|implement|add|create|fix|bug|error|design|refactor|debug|investigate|調査|移行|削除|変更|更新|テスト|test|review|レビュー)'; then
  ACTIVATE=" タスク検出: 作業開始前に pce_memory_activate を実行すること（ユーザーのプロンプトからキーワードを抽出し q に設定、scope: project/principle、結果は内部参照のみ）。"
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

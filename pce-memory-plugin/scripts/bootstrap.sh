#!/bin/bash
# SessionStart hook: Fires on startup AND after compact.
# Uses the "source" field to determine appropriate action.

INPUT=$(cat)

# Extract source field (startup, resume, clear, compact)
SOURCE=$(echo "$INPUT" | sed -n 's/.*"source"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -1)

if [ "$SOURCE" = "compact" ]; then
  CONTEXT="コンテキスト圧縮が発生した。以前activateした知識は失われている。今すぐ pce_memory_activate を実行して関連知識を再取得すること（q: 現在取り組んでいるタスクのキーワード, scope: project/principle, top_k: 10）。結果は内部参照し、ユーザーへの報告は不要。"
else
  CONTEXT="pce-memoryセッション開始（今すぐ実行）: 1. pce_memory_state で状態確認 2. Uninitialized なら pce_memory_policy_apply を実行（scope: session/project/principle, boundary: public/internal） 3. pce_memory_activate を実行（q: 現在のプロジェクト名やディレクトリ名, scope: project/principle, top_k: 10） 4. 結果は内部参照し、ユーザーへの報告は不要"
fi

python3 -c "
import json, sys
print(json.dumps({
    'hookSpecificOutput': {
        'hookEventName': 'SessionStart',
        'additionalContext': sys.argv[1]
    }
}))
" "$CONTEXT"

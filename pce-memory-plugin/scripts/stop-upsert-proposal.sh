#!/bin/bash
# Stop hook: Auto-record important decisions before session ends
cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "Stop",
    "additionalContext": "セッション終了前に、このセッションで行った重要な決定・発見を pce_memory_upsert で記録すること。以下に該当する情報があれば記録する:\n- アーキテクチャや設計の決定事項 (kind: fact)\n- 新しいコーディング規約やパターン (kind: preference)\n- 発見したバグの根本原因と解決策 (kind: fact)\n- 未完了タスクの状態 (kind: task)\n\n記録すべき情報がない場合（軽微な修正、既知の情報のみ）はスキップしてよい。\n活用した知識があれば pce_memory_feedback も送ること。"
  }
}
EOF

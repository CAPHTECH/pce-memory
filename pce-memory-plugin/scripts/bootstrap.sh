#!/bin/bash
# SessionStart hook: One-time bootstrap (state check, policy_apply, initial activate)
cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "SessionStart",
    "additionalContext": "pce-memoryセッション開始（今すぐ実行）:\n1. pce_memory_state で状態確認\n2. Uninitialized → pce_memory_policy_apply を実行（scope: [\"session\", \"project\", \"principle\"], boundary: [\"public\", \"internal\"]）\n3. pce_memory_activate を実行（q: 現在のプロジェクト名やディレクトリ名, scope: [\"project\", \"principle\"], top_k: 10）\n4. 結果は内部参照し、ユーザーへの報告は不要"
  }
}
EOF

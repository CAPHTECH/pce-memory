#!/bin/bash
# SessionStart hook: Bootstrap pce-memory and inject operating protocol
cat <<'EOF'
{
  "hookSpecificOutput": {
    "hookEventName": "SessionStart",
    "additionalContext": "## pce-memory 自律運用プロトコル\n\nあなたはpce-memoryを自律的に運用する。ユーザーに操作を求めず、自分で判断して実行すること。\n\n### セッション開始（今すぐ実行）\n1. pce_memory_state で状態確認\n2. Uninitialized → pce_memory_policy_apply を実行（scope: [\"session\", \"project\", \"principle\"], boundary: [\"public\", \"internal\"]）\n3. pce_memory_activate を実行（q: 現在のプロジェクト名やディレクトリ名, scope: [\"project\", \"principle\"], top_k: 10）\n\n### タスク開始時（自動）\n- 新しいタスクを受けたら、まず pce_memory_activate で関連知識を想起する\n- クエリはユーザーの意図からキーワードを抽出して構成する\n- 想起した知識は内部的に参照し、作業に反映する（ユーザーへの逐一報告は不要）\n\n### 作業中（自動）\n- 重要な設計決定をしたら pce_memory_upsert で即座に記録する\n- エンティティやリレーションの追加が適切な場合は pce_memory_upsert_entity / pce_memory_upsert_relation も実行する\n- 想起した知識が役立った/古かった場合は pce_memory_feedback を送る\n\n### 記録の判断基準\n- 記録する: アーキテクチャ決定、技術的制約、API仕様、命名規則、バグの根本原因\n- 記録しない: 軽微な修正、一時的な作業状態、自明な情報、secret情報\n\n### upsert 時の必須フィールド\n- text: 簡潔かつ具体的（1-2文）\n- kind: fact/preference/task/policy_hint\n- scope: session/project/principle\n- boundary_class: public/internal（pii/secretは避ける）\n- content_hash: テキストのSHA256\n- provenance: { at: ISO8601, actor: \"claude\", note: \"経緯\" }"
  }
}
EOF

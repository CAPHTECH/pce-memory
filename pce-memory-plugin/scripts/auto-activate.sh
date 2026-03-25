#!/bin/bash
# UserPromptSubmit hook: Inject pce-memory v2 protocol on every user message.
# Task-like prompts get intent-aware activate instruction.

INPUT=$(cat)

# Extract the user prompt text using python3 for robust JSON parsing
PROMPT=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('userPrompt',''))" 2>/dev/null || true)

# Base protocol (always injected) — v2 API
BASE="pce-memory v2 autonomous operation: Before the first non-state pce_memory call in this turn, check pce_memory_state. State guard: Uninitialized → run pce_memory_policy_apply; PolicyApplied → upsert allowed but skip activate/feedback; HasClaims → upsert/activate allowed but skip feedback; Ready → all tools allowed. For durable knowledge, prefer observe → distill → promote over direct upsert. Direct upsert is only for already-distilled knowledge with provenance. When graph structure is obvious and you use pce_memory_upsert, include entities and relations in the same call so the client registers technologies, files, modules, and concepts explicitly; do not assume server-side extraction. session scope upsert is rejected; use observe instead. secret boundary_class upsert is rejected; use observe for secret material. Send pce_memory_feedback when recalled knowledge was helpful/outdated (Ready state only). Record: architecture decisions, technical constraints, API specs, naming conventions, bug root causes. Do NOT record: minor fixes, obvious info, secrets. After context compaction, re-retrieve knowledge with pce_memory_activate if previously activated knowledge is no longer in conversation. Always write upsert text and activate queries in English for consistent embedding search and team sync."

# Intent-aware task detection
ACTIVATE=""
if echo "$PROMPT" | grep -qiE '(fix|bug|error|debug|investigate|crash|fail|broken)'; then
  ACTIVATE=" Task detected (debug_incident): if state is HasClaims or Ready, run pce_memory_activate(intent: 'debug_incident', include_observations: true, q: <keywords>, scope: [project], allow: ['answer:task'], top_k: 10) before starting work."
elif echo "$PROMPT" | grep -qiE '(design|architect|decide|choose|compare|tradeoff|ADR)'; then
  ACTIVATE=" Task detected (design_decision): if state is HasClaims or Ready, run pce_memory_activate(intent: 'design_decision', q: <keywords>, scope: [project, principle], memory_type_filter: ['knowledge', 'procedure', 'norm'], allow: ['answer:task'], top_k: 10) before starting work."
elif echo "$PROMPT" | grep -qiE '(policy|security|compliance|rule|enforce|boundary|invariant)'; then
  ACTIVATE=" Task detected (policy_check): if state is HasClaims or Ready, run pce_memory_activate(intent: 'policy_check', q: <keywords>, scope: [project, principle], memory_type_filter: ['norm', 'knowledge'], allow: ['answer:task'], top_k: 10) before starting work."
elif echo "$PROMPT" | grep -qiE '(implement|add|create|build|refactor|migrate|delete|remove|change|update|modify|test|review|deploy|configure|setup|install|upgrade|continue|resume)'; then
  ACTIVATE=" Task detected (resume_task): if state is HasClaims or Ready, run pce_memory_activate(intent: 'resume_task', include_observations: true, q: <keywords>, scope: [project], allow: ['answer:task'], top_k: 10) before starting work."
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

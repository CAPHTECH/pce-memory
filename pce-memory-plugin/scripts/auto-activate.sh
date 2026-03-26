#!/bin/bash
# UserPromptSubmit hook: Inject pce-memory v2 protocol on every user message.
# Task-like prompts get intent-aware activate instruction.

INPUT=$(cat)

# Extract the user prompt text using python3 for robust JSON parsing
PROMPT=$(echo "$INPUT" | python3 -c "import sys,json; d=json.load(sys.stdin); print(d.get('userPrompt',''))" 2>/dev/null || true)

# Base protocol (always injected) — v2 API
BASE="pce-memory v2 autonomous operation: Start each new task with pce_memory_state; if Uninitialized, run pce_memory_policy_apply. Use memory when it will reduce rework: task resume, debugging, design decisions, recurring incidents, cross-module contracts, migrations, or runbooks. Skip heavy memory work for short single-file edits where code and tests are the only source of truth. Use pce_memory_observe for raw notes, logs, session state, tool output, and secrets — treat observations as scratchpad, not durable knowledge. Prefer observe → distill → promote in the same task when you confirm something reusable. Promote durable claims for project- or principle-level contracts such as invariants, recovery rules, search semantics, migration constraints, and runbook steps. Keep scope: session for transient findings; use scope: project or scope: principle only after the claim is validated and likely to matter in future sessions. If activate returns only transient observations, use them as resume context but do not over-trust them — re-check code, tests, or logs before making design claims. Use pce_memory_upsert only for already-distilled durable knowledge with provenance; include entities and relations when graph structure is obvious. Never upsert with scope: session or boundary_class: secret. Send pce_memory_feedback only for durable claim_id values that were activated and actually used — mark claims helpful, outdated, harmful, duplicate, or completed so retrieval quality improves over time. After context compaction, re-retrieve knowledge with pce_memory_activate if previously activated knowledge is no longer in conversation. Always write upsert text and activate queries in English for consistent embedding search and team sync."

# Intent-aware task detection — activate with a short English query naming the contract or decision needed
ACTIVATE=""
if echo "$PROMPT" | grep -qiE '(fix|bug|error|debug|investigate|crash|fail|broken)'; then
  ACTIVATE=" Task detected (debug_incident): before starting work, run pce_memory_activate(intent: 'debug_incident', include_observations: true, q: <short English query naming the contract or error>, scope: [project], allow: ['answer:task'], top_k: 10)."
elif echo "$PROMPT" | grep -qiE '(design|architect|decide|choose|compare|tradeoff|ADR)'; then
  ACTIVATE=" Task detected (design_decision): before starting work, run pce_memory_activate(intent: 'design_decision', q: <short English query naming the decision needed>, scope: [project, principle], memory_type_filter: ['knowledge', 'procedure', 'norm'], allow: ['answer:task'], top_k: 10)."
elif echo "$PROMPT" | grep -qiE '(policy|security|compliance|rule|enforce|boundary|invariant)'; then
  ACTIVATE=" Task detected (policy_check): before starting work, run pce_memory_activate(intent: 'policy_check', q: <short English query naming the policy or invariant>, scope: [project, principle], memory_type_filter: ['norm', 'knowledge'], allow: ['answer:task'], top_k: 10)."
elif echo "$PROMPT" | grep -qiE '(implement|add|create|build|refactor|migrate|delete|remove|change|update|modify|test|review|deploy|configure|setup|install|upgrade|continue|resume)'; then
  ACTIVATE=" Task detected (resume_task): before starting work, run pce_memory_activate(intent: 'resume_task', include_observations: true, q: <short English query naming the contract or module>, scope: [project], allow: ['answer:task'], top_k: 10)."
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

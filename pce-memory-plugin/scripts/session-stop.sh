#!/bin/bash
# Stop hook: Instruct Claude to persist session context before ending

python3 -c "
import json
print(json.dumps({
    'continue': True,
    'stopReason': 'pce-memory session persistence',
    'systemMessage': 'Session ending. Persist important context using the v2 workflow. Step 1 - Close completed tasks: For any task claims (kind: task) recalled via activate that are now done, send pce_memory_feedback(claim_id, signal: completed). Step 2 - Record incomplete task state (PRIORITY if work is in progress): Call pce_memory_upsert with kind=task, scope=project, boundary_class=internal, memory_type=working_state, provenance with current ISO timestamp. Text format: TASK [status:in_progress|blocked] description. Progress: what was done. Next: next steps. Blockers: blockers or none. Always write in English. Step 3 - Promote durable discoveries: For confirmed project- or principle-level contracts (invariants, recovery rules, search semantics, migration constraints, runbook steps): prefer pce_memory_observe then pce_memory_distill then pce_memory_promote. Use pce_memory_upsert only for already-distilled knowledge with provenance. Include entities and relations when graph structure is obvious. Use pce_memory_link_claims to connect related claims (supports/extends/contradicts/related). Never upsert scope: session or boundary_class: secret. Skip this step for minor fixes or obvious info. Step 4 - Send feedback: pce_memory_feedback only for durable claim_id values that were activated and actually used in this session (helpful/outdated/harmful/duplicate/completed). Step 5 - Graph maintenance (optional, only if many claims were added): Run pce_memory_graph_audit to check for orphans, contradiction cycles, or scope holes. Address critical findings before ending. After completing all steps, allow the session to end.'
}))
"

#!/bin/bash
# Stop hook: Instruct Claude to persist session context before ending

python3 -c "
import json
print(json.dumps({
    'continue': True,
    'stopReason': 'pce-memory session persistence',
    'systemMessage': 'Session ending. Persist important context for continuity using the v2 workflow: Step 1 - Close completed tasks: For any task claims (kind: task) recalled via activate that are now done, send pce_memory_feedback(claim_id, signal: outdated). If the completed work produced important outcomes, record them as durable knowledge (see Step 3). Step 2 - Record incomplete task state (PRIORITY if work is in progress): Call pce_memory_upsert with kind=task, scope=project, boundary_class=internal, memory_type=working_state, provenance with current ISO timestamp. Text format: TASK [status:in_progress|blocked] description. Progress: what was done. Next: next steps. Blockers: blockers or none. Always write in English. Step 3 - Record durable discoveries: For confirmed architecture decisions, conventions, or bug root causes: Option A (preferred): pce_memory_observe then pce_memory_distill then pce_memory_promote with provenance. Option B (for already-distilled knowledge): pce_memory_upsert with kind=fact/preference, scope=project/principle, memory_type=knowledge/procedure/norm, and provenance. Include entities and relations when structure is clear. Do NOT upsert session scope or secret boundary_class. Step 4 - Send feedback: pce_memory_feedback for any recalled knowledge used (helpful/outdated/harmful). After completing all steps, allow the session to end.'
}))
"

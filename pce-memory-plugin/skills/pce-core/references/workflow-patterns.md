# PCE Memory Workflow Patterns

## Pattern 1: New Feature Implementation

```
1. activate({
     q: "related feature design API",
     scope: ["project", "principle"],
     allow: ["answer:task"],
     intent: "design_decision",
     kind_filter: ["fact", "preference", "policy_hint"],
     memory_type_filter: ["knowledge", "procedure", "norm"]
   })
   → Review existing design decisions and conventions

2. Implement (considering recalled knowledge)

3. observe({
     source_type: "chat",
     content: "Design decision draft and local evidence",
     boundary_class: "internal"
   })
   → Preserve raw context and evidence

4. distill({
     source_observation_ids: ["obs_..."],
     proposed_kind: "fact",
     proposed_scope: "project",
     proposed_memory_type: "knowledge"
   })
   → Create a reviewable candidate

5. promote({
     candidate_id: "pq_...",
     provenance: { "at": "...", "actor": "claude" }
   })
   → Record new decision

6. feedback({ claim_id: "clm_xxx", signal: "helpful" })
   → Feedback on useful knowledge
```

## Pattern 2: Bug Fix

```
1. activate({
     q: "error message related component",
     scope: ["project"],
     allow: ["answer:task"],
     intent: "debug_incident",
     include_observations: true,
     memory_type_filter: ["working_state", "knowledge", "procedure"]
   })
   → Check past similar issues, procedures, and recent evidence

2. Identify root cause and fix

3. observe({
     source_type: "chat",
     content: "Root cause notes, logs, failing conditions, and fix evidence",
     boundary_class: "internal"
   })

4. distill({
     source_observation_ids: ["obs_..."],
     proposed_kind: "fact",
     proposed_scope: "project",
     proposed_memory_type: "knowledge"
   })

5. promote({
     candidate_id: "pq_...",
     provenance: { "at": "...", "actor": "claude" }
   })
   → Record for future reference
```

## Pattern 3: Code Review

```
1. activate({
     q: "coding conventions naming style",
     scope: ["project", "principle"],
     allow: ["answer:task"],
     intent: "design_decision",
     memory_type_filter: ["knowledge", "procedure", "norm"]
   })
   → Review project conventions

2. Perform review (based on conventions)

3. If new convention is ratified, distill/promote it as `preference + procedure|knowledge`
```

## Pattern 4: Refactoring

```
1. activate({
     q: "architecture patterns dependencies",
     scope: ["project"],
     allow: ["answer:task"],
     intent: "design_decision",
     memory_type_filter: ["knowledge", "procedure"]
   })
   → Confirm current design intent

2. Perform refactoring

3. Distill and promote the new rationale if the architecture contract changed
```

## Pattern 5: Design Discussion

```
1. activate({
     q: "design patterns tradeoffs",
     scope: ["project", "principle"],
     allow: ["answer:task"],
     intent: "design_decision",
     memory_type_filter: ["knowledge", "procedure", "norm"]
   })
   → Review existing decisions and principles

2. Compare and evaluate options

3. Observe discussion notes and tradeoff evidence

4. Distill the chosen design into a candidate

5. Promote after review lineage is ready
```

## Pattern 6: Invalid Durable Memory

```
1. activate({
     q: "obsolete design decision",
     scope: ["project", "principle"],
     allow: ["answer:task"],
     intent: "policy_check"
   })
   → Confirm the affected durable claim

2. rollback({
     claim_id: "clm_...",
     reason: "superseded by new architecture",
     provenance: { "at": "...", "actor": "claude" }
   })
   → Append-only repair path
```

## Anti-patterns

- **Skipping distill/promote**: Raw observations must not bypass the reviewable promotion path
- **Using upsert for session state**: Session working context belongs in `observe`
- **Recording secrets durably**: Never upsert secrets; keep them in raw observation only if necessary
- **Vague text**: "Decided various things" → "Set auth token expiry to 15 minutes"
- **Forgetting feedback**: Quality feedback on activated knowledge improves precision

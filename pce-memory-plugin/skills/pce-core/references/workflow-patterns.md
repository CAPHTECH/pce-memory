# PCE Memory Workflow Patterns

## Pattern 1: New Feature Implementation

```
1. activate({ q: "related feature design api", scope: ["project", "principle"], allow: ["answer:task"] })
   → Review existing design decisions and conventions

2. Implement (considering recalled knowledge)

3. upsert({
     text: "Decision: <specific design decision>. Reason: <why>.",
     kind: "fact",
     scope: "project",
     boundary_class: "internal"
   })
   → Record new decision

4. feedback({ claim_id: "clm_xxx", signal: "helpful" })
   → Feedback on useful knowledge
```

## Pattern 2: Bug Fix

```
1. activate({ q: "error message related component", scope: ["project", "session"], allow: ["answer:task"] })
   → Check past similar issues and related implementations

2. Identify root cause and fix

3. upsert({
     text: "Root cause: <cause>. Fix: <fix>.",
     kind: "fact",
     scope: "project"
   })
   → Record for future reference
```

## Pattern 3: Code Review

```
1. activate({ q: "coding conventions naming style", scope: ["project", "principle"], allow: ["answer:task"] })
   → Review project conventions

2. Perform review (based on conventions)

3. If new convention established → upsert({ kind: "preference" })
```

## Pattern 4: Refactoring

```
1. activate({ q: "architecture patterns dependencies", scope: ["project"], allow: ["answer:task"] })
   → Confirm current design intent

2. Perform refactoring

3. upsert({
     text: "Decision: refactor <area> to <new structure>. Reason: <why>.",
     kind: "fact",
     scope: "project"
   })
```

## Pattern 5: Design Discussion

```
1. activate({ q: "design patterns tradeoffs", scope: ["project", "principle"], allow: ["answer:task"] })
   → Review existing decisions and principles

2. Compare and evaluate options

3. upsert({
     text: "Decision: <chosen design>. Reason: <tradeoff and rationale>.",
     kind: "fact",
     scope: "project"
   })
```

## Anti-patterns

- **Recording everything**: Be selective — important decisions only
- **Vague text**: "Decided various things" → "Set auth token expiry to 15 minutes"
- **Recording secrets**: Never record API keys or passwords
- **Forgetting feedback**: Quality feedback on activated knowledge improves precision
- **Recording completed tasks as new task claims**: Close them with feedback and record only durable outcomes

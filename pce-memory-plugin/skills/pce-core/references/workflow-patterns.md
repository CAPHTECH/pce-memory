# PCE Memory Workflow Patterns

## Pattern 1: New Feature Implementation

```
1. activate({ q: "related feature design API", scope: ["project", "principle"] })
   → Review existing design decisions and conventions

2. Implement (considering recalled knowledge)

3. upsert({
     text: "Specific design decision",
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
1. activate({ q: "error message related component", scope: ["project", "session"] })
   → Check past similar issues and related implementations

2. Identify root cause and fix

3. upsert({
     text: "Root cause and fix",
     kind: "fact",
     scope: "project"
   })
   → Record for future reference
```

## Pattern 3: Code Review

```
1. activate({ q: "coding conventions naming style", scope: ["project", "principle"] })
   → Review project conventions

2. Perform review (based on conventions)

3. If new convention established → upsert({ kind: "preference" })
```

## Pattern 4: Refactoring

```
1. activate({ q: "architecture patterns dependencies", scope: ["project"] })
   → Confirm current design intent

2. Perform refactoring

3. upsert({
     text: "Refactoring rationale and new structure",
     kind: "fact",
     scope: "project"
   })
```

## Pattern 5: Design Discussion

```
1. activate({ q: "design patterns tradeoffs", scope: ["project", "principle"] })
   → Review existing decisions and principles

2. Compare and evaluate options

3. upsert({
     text: "Chosen design and rationale (ADR format recommended)",
     kind: "fact",
     scope: "project"
   })
```

## Anti-patterns

- **Recording everything**: Be selective — important decisions only
- **Vague text**: "Decided various things" → "Set auth token expiry to 15 minutes"
- **Recording secrets**: Never record API keys or passwords
- **Forgetting feedback**: Quality feedback on activated knowledge improves precision

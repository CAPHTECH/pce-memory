# pce-memory

PCE Memory - MCP Server for Process-Context Engine

## Overview

PCE Memory is the official MCP server implementation of Process-Context Engine (PCE).
It provides context memory, retrieval, and integration capabilities for agents and LLM applications.

## MCP Configuration

> **Note:** Replace `your-project` with your actual project name to keep databases separate per project.

### Claude Desktop

Add to `~/Library/Application Support/Claude/claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "pce-memory": {
      "command": "npx",
      "args": ["-y", "pce-memory"],
      "env": {
        "PCE_DB": "~/.pce/your-project.db"
      }
    }
  }
}
```

### Claude Code

Add to `.mcp.json` in your project root:

```json
{
  "mcpServers": {
    "pce-memory": {
      "command": "npx",
      "args": ["-y", "pce-memory"],
      "env": {
        "PCE_DB": "~/.pce/your-project.db"
      }
    }
  }
}
```

### Cline / Roo Code

Add to VS Code settings (`settings.json`):

```json
{
  "cline.mcpServers": {
    "pce-memory": {
      "command": "npx",
      "args": ["-y", "pce-memory"],
      "env": {
        "PCE_DB": "~/.pce/your-project.db"
      }
    }
  }
}
```

## Features

- **MCP Protocol Support**: Model Context Protocol (MCP) v1.0.4 compliant
- **Pace Layering**: Three-tier scope management (session / project / principle)
- **Boundary-First Security**: Scope-based boundary management with Redact-before-send
- **Hybrid Search**: Full-text search + Vector similarity search
- **DuckDB Storage**: Fast local storage with embedded DuckDB
- **Local Embeddings**: Local embedding generation via transformers.js

## Quick Start

```bash
# Run directly with npx
npx pce-memory

# Or install globally
npm install -g pce-memory
pce-memory
```

## Commands

| Command            | Description                     |
| ------------------ | ------------------------------- |
| `pce-memory`       | MCP client (auto-starts daemon) |
| `pce-daemon`       | Standalone daemon process       |
| `pce-memory-stdio` | Direct stdio mode (no daemon)   |

## MCP Tools

### pce_memory_policy_apply

Apply policy (initialization)

```typescript
{
  yaml?: string  // Policy YAML (uses default if omitted)
}
```

### pce_memory_upsert

Register a claim (knowledge fragment)

```typescript
{
  text: string,           // Claim content
  kind: "fact" | "preference" | "task" | "policy_hint",
  scope: "session" | "project" | "principle",
  boundary_class: "public" | "internal" | "pii" | "secret",
  content_hash: string,   // Format: sha256:...
  provenance: {           // Origin info (required)
    at: string,           // ISO 8601 timestamp
    actor?: string,
    url?: string,
    note?: string
  }
}
```

### pce_memory_activate

Build active context (AC)

```typescript
{
  scope: string[],        // Target scopes
  allow: string[],        // Allowed boundary classes
  q?: string,             // Search query
  top_k?: number          // Number of results (default: 10)
}
```

### pce_memory_boundary_validate

Pre-generation boundary check

```typescript
{
  payload: string,        // Text to validate
  scope?: string,
  allow?: string[]
}
```

### pce_memory_feedback

Update critic (adopt/reject/stale/duplicate)

```typescript
{
  claim_id: string,
  signal: "helpful" | "harmful" | "outdated" | "duplicate",
  score?: number          // -1.0 to 1.0
}
```

### pce_memory_state

Get current state

```typescript
// Returns: { state: "Uninitialized" | "PolicyApplied" | "HasClaims" | "Ready" }
```

## State Machine

```
Uninitialized
     │
     │ policy_apply
     ▼
PolicyApplied
     │
     │ upsert
     ▼
 HasClaims
     │
     │ activate
     ▼
   Ready ◄──┐
     │      │
     └──────┘ (activate/upsert/feedback)
```

## Pace Layering (Scope)

| Scope       | Change Rate | Use Case                                |
| ----------- | ----------- | --------------------------------------- |
| `session`   | Fast        | Session-specific temporary information  |
| `project`   | Medium      | Project-specific patterns and decisions |
| `principle` | Slow        | Universal principles and best practices |

## Requirements

- Node.js >= 22.18.0

## License

MIT

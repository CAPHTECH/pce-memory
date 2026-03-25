// ========== MCP Prompts (Issue #16) ==========

/**
 * Prompt定義型
 */
export interface PromptDefinition {
  name: string;
  description?: string;
  arguments?: Array<{
    name: string;
    description?: string;
    required?: boolean;
  }>;
}

/**
 * Promptメッセージ型
 */
export interface PromptMessage {
  role: 'user' | 'assistant';
  content: {
    type: 'text';
    text: string;
  };
}

/**
 * 定義済みPrompts一覧
 */
export const PROMPTS_DEFINITIONS: PromptDefinition[] = [
  {
    name: 'recall_context',
    description: 'Guide for recalling relevant knowledge before starting a task',
    arguments: [
      {
        name: 'query',
        description: 'Search query (e.g., "authentication", "API design")',
        required: false,
      },
      {
        name: 'scope',
        description: 'Scope (session/project/principle)',
        required: false,
      },
    ],
  },
  {
    name: 'record_decision',
    description: 'Guide for recording design decisions',
    arguments: [
      {
        name: 'topic',
        description: 'Decision topic (e.g., "state management library selection")',
        required: true,
      },
    ],
  },
  {
    name: 'sync_workflow',
    description: 'Guide for Git sync workflow (push/pull/status)',
    arguments: [
      {
        name: 'operation',
        description: 'Operation type (push/pull/status)',
        required: false,
      },
    ],
  },
  {
    name: 'sync_push',
    description: 'Guide for exporting local knowledge to .pce-shared/ directory',
    arguments: [
      {
        name: 'scope_filter',
        description: 'Filter by scope (e.g., "project,principle")',
        required: false,
      },
      {
        name: 'boundary_filter',
        description: 'Filter by boundary class (e.g., "public,internal")',
        required: false,
      },
    ],
  },
  {
    name: 'sync_pull',
    description: 'Guide for importing shared knowledge from .pce-shared/ directory',
    arguments: [
      {
        name: 'dry_run',
        description: 'Preview changes without applying (true/false)',
        required: false,
      },
      {
        name: 'since',
        description: 'Incremental import from date (ISO8601)',
        required: false,
      },
    ],
  },
  {
    name: 'debug_assist',
    description: 'Guide for searching related knowledge during debugging',
    arguments: [
      {
        name: 'error_message',
        description: 'Error message or keyword',
        required: false,
      },
    ],
  },
];

/**
 * Generate prompt messages
 */
function generatePromptMessages(
  prompt: PromptDefinition,
  args?: Record<string, string>
): PromptMessage[] {
  switch (prompt.name) {
    case 'recall_context': {
      const query = args?.['query'] || '<keyword to search>';
      const scope = args?.['scope'] || 'project';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Before starting a task, I want to recall relevant knowledge. Search query: "${query}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce_memory_activate to recall relevant knowledge.

\`\`\`json
{
  "q": "${query}",
  "scope": ["${scope}"],
  "allow": ["answer:*"],
  "top_k": 10
}
\`\`\`

## Usage Tips

1. **Scope Selection**:
   - \`session\`: Information limited to current conversation
   - \`project\`: Project-specific patterns and conventions
   - \`principle\`: Universal principles (SOLID, TDD, etc.)

2. **Query Tips**:
   - Use space-separated keywords (OR search)
   - Use specific keywords ("JWT authentication" rather than "auth")

3. **Post-recall Actions**:
   - Send \`helpful\` feedback for useful knowledge
   - Send \`outdated\` for stale information
   - When \`maintenance_hints\` are present, consolidate \`similar_pairs\`, send feedback for \`high_retrieval_no_feedback\`, and distill \`unprocessed_observations\` backlog`,
          },
        },
      ];
    }

    case 'record_decision': {
      const topic = args?.['topic'] || '<decision topic>';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to record a design decision. Topic: "${topic}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce_memory_upsert to record the design decision.

\`\`\`json
{
  "text": "Decision on ${topic}: <describe the decision>",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal",
  "content_hash": "sha256:<SHA256 hash of text>",
  "provenance": {
    "at": "<current ISO8601 datetime>",
    "actor": "claude",
    "note": "ADR-XXXX / Issue #YYY"
  }
}
\`\`\`

## Recording Guidelines

1. **Kind Selection**:
   - \`fact\`: Architecture decisions, technical constraints
   - \`preference\`: Coding styles, tool choices
   - \`task\`: Work in progress, TODOs
   - \`policy_hint\`: Security requirements, operational rules

2. **Boundary Class**:
   - \`public\`: Publicly shareable information
   - \`internal\`: Internal use only
   - \`pii\`: Contains personal information
   - \`secret\`: Credentials (rejected by default in upsert; use observe)

3. **Provenance**:
   - \`at\`: Required. Recording timestamp
   - \`actor\`: Recorder (claude/user)
   - \`note\`: Reference to ADR number or Issue number`,
          },
        },
      ];
    }

    case 'sync_workflow': {
      const operation = args?.['operation'] || 'status';
      const operationGuides: Record<string, string> = {
        push: `## Push: Export Local Knowledge

Use pce_memory_sync_push to export knowledge from the local DB to .pce-shared/.

\`\`\`json
{
  "scope_filter": ["project", "principle"],
  "boundary_filter": ["public", "internal"]
}
\`\`\`

### Options
- \`target_dir\`: Export destination (default: .pce-shared at Git root if available)
- \`scope_filter\`: Filter by scope
- \`boundary_filter\`: Filter by boundary_class (secret is always excluded)
- \`since\`: Export only changes after the specified datetime

### Notes
- Information with secret boundary is automatically excluded
- pii is only included when explicitly specified`,

        pull: `## Pull: Import Shared Knowledge

Use pce_memory_sync_pull to import knowledge from .pce-shared/.

\`\`\`json
{
  "dry_run": true
}
\`\`\`

### Options
- \`source_dir\`: Import source (default: .pce-shared at Git root if available)
- \`scope_filter\`: Filter by scope
- \`boundary_filter\`: Filter by boundary_class
- \`dry_run\`: Preview changes without applying when true
- \`since\`: Incremental import (only after the specified datetime)

### CRDT Merge Strategy
- Claims with same content_hash are skipped as duplicates
- boundary_class can only be upgraded (public→internal), not downgraded
- Conflicts are auto-resolved (boundary_upgrade) or skipped`,

        status: `## Status: Check Sync State

Use pce_memory_sync_status to check the state of the sync directory.

\`\`\`json
{}
\`\`\`

### Available Information
- \`exists\`: Directory existence
- \`manifest\`: Version, last push/pull timestamps
- \`files\`: File counts for claims/entities/relations
- \`validation\`: JSON schema validation results`,
      };

      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Tell me how to use Git sync functionality. Operation: ${operation}`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text:
              operationGuides[operation] ||
              `# Git-based CRDT Sync

pce-memory allows synchronizing knowledge across teams via Git.

## Basic Workflow

1. **status** - Check current sync state
2. **pull** - Import shared knowledge (dry_run: true for preview)
3. **work** - Record and update knowledge
4. **push** - Export local knowledge
5. **git commit/push** - Share changes via Git

## CLI Commands

\`\`\`bash
pce-memory sync status
pce-memory sync pull --dry-run
pce-memory sync push
\`\`\`

## Git Hooks Integration

Automatic sync with pre-commit and post-merge hooks:
\`\`\`bash
./scripts/git-hooks/install-hooks.sh
export PCE_SYNC_ENABLED=true
\`\`\``,
          },
        },
      ];
    }

    case 'sync_push': {
      const scopeFilter = args?.['scope_filter'] || 'project,principle';
      const boundaryFilter = args?.['boundary_filter'] || 'public,internal';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to export local knowledge to share with the team.`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce_memory_sync_push to export knowledge to .pce-shared/ directory.

\`\`\`json
{
  "scope_filter": ["${scopeFilter.split(',').join('", "')}"],
  "boundary_filter": ["${boundaryFilter.split(',').join('", "')}"],
  "include_entities": true,
  "include_relations": true
}
\`\`\`

## Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| \`target_dir\` | .pce-shared | Export destination directory |
| \`scope_filter\` | project, principle | Filter by scope (session excluded by default) |
| \`boundary_filter\` | public, internal | Filter by boundary class |
| \`since\` | - | Export only claims updated after this ISO8601 datetime |
| \`include_entities\` | true | Include graph entities in export |
| \`include_relations\` | true | Include graph relations in export |

## Security Notes

- \`secret\` boundary is **always excluded** from export
- \`pii\` is only included when explicitly specified in boundary_filter
- Review exported files before committing to Git

## After Push

\`\`\`bash
# Stage the exported files
git add .pce-shared/

# Commit and push
git commit -m "chore: update shared knowledge"
git push
\`\`\``,
          },
        },
      ];
    }

    case 'sync_pull': {
      const since = args?.['since'] || '';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `I want to import shared knowledge from the team.`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce_memory_sync_pull to import knowledge from .pce-shared/ directory.

## Step 1: Preview Changes (Recommended)

\`\`\`json
{
  "dry_run": true
}
\`\`\`

## Step 2: Apply Changes

\`\`\`json
{
  "dry_run": false${since ? `,\n  "since": "${since}"` : ''}
}
\`\`\`

## Options

| Parameter | Default | Description |
|-----------|---------|-------------|
| \`source_dir\` | .pce-shared | Import source directory |
| \`scope_filter\` | all | Filter by scope |
| \`boundary_filter\` | all except secret | Filter by boundary class |
| \`dry_run\` | false | Preview without applying changes |
| \`since\` | - | Incremental import from ISO8601 datetime |

## CRDT Merge Behavior

| Scenario | Behavior |
|----------|----------|
| Same content_hash exists | Skip (duplicate) |
| boundary_class differs | Upgrade only (public→internal) |
| Entity/relation conflict | Skip with warning |

## Best Practices

1. **Always dry_run first**: Preview changes before applying
2. **Use incremental import**: Specify \`since\` for large knowledge bases
3. **Review conflicts**: Check skipped items in the result
4. **Pull before push**: Avoid overwriting team's changes`,
          },
        },
      ];
    }

    case 'debug_assist': {
      const errorMessage = args?.['error_message'] || '<error message>';
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `An error occurred during debugging: "${errorMessage}"`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: `Use pce_memory_activate to search for past similar issues and solutions.

\`\`\`json
{
  "q": "${errorMessage}",
  "scope": ["project", "session"],
  "allow": ["answer:*"],
  "top_k": 15
}
\`\`\`

## Leveraging Knowledge During Debugging

1. **Search by error message**: Check if there's a record of solving the same error before
2. **Search by related component**: Check known issues for the module where the error occurred
3. **Record after resolution**: Use \`upsert\` to record new solutions

## Query Tips

- Include error codes (e.g., "ECONNREFUSED", "TypeError")
- Include library names (e.g., "DuckDB lock")
- Include symptoms (e.g., "timeout", "memory leak")

## Example of Recording a Solution

\`\`\`json
{
  "text": "DuckDB 'Could not set lock on file' error: Need to explicitly close socket with server.close()",
  "kind": "fact",
  "scope": "project",
  "boundary_class": "internal"
}
\`\`\``,
          },
        },
      ];
    }

    default:
      return [
        {
          role: 'user',
          content: {
            type: 'text',
            text: `Tell me about ${prompt.name}`,
          },
        },
        {
          role: 'assistant',
          content: {
            type: 'text',
            text: prompt.description || 'No description available for this prompt.',
          },
        },
      ];
  }
}

/**
 * prompts/list ハンドラ
 */
export async function handleListPrompts(args: Record<string, unknown>): Promise<{
  prompts: PromptDefinition[];
}> {
  const { cursor } = args as { cursor?: string };

  // ページネーション処理
  const PAGE_SIZE = 10;
  const parsedCursor = cursor ? parseInt(cursor, 10) : 0;
  const startIdx = Number.isFinite(parsedCursor) && parsedCursor >= 0 ? parsedCursor : 0;
  const prompts = PROMPTS_DEFINITIONS.slice(startIdx, startIdx + PAGE_SIZE);

  return { prompts };
}

/**
 * prompts/get ハンドラ
 */
export async function handleGetPrompt(args: Record<string, unknown>): Promise<{
  description?: string;
  messages: PromptMessage[];
}> {
  const { name, arguments: promptArgs } = args as {
    name?: string;
    arguments?: Record<string, string>;
  };

  if (!name) {
    throw new Error('name is required');
  }

  const prompt = PROMPTS_DEFINITIONS.find((p) => p.name === name);
  if (!prompt) {
    throw new Error(`Prompt not found: ${name}`);
  }

  // 必須引数のバリデーション
  if (prompt.arguments) {
    for (const arg of prompt.arguments) {
      if (arg.required && (!promptArgs || !(arg.name in promptArgs))) {
        throw new Error(`Required argument missing: ${arg.name}`);
      }
    }
  }

  const messages = generatePromptMessages(prompt, promptArgs);

  // exactOptionalPropertyTypes対応: undefinedは含めない
  return {
    ...(prompt.description !== undefined && { description: prompt.description }),
    messages,
  };
}

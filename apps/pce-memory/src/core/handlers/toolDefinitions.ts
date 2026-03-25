import { CLAIM_KINDS, MEMORY_TYPES, ACTIVATE_INTENTS } from '../../domain/types.js';
import { CLAIM_LINK_TYPES } from '../../store/claimLinks.js';

// ========== Tool Definitions ==========

export const TOOL_DEFINITIONS = [
  {
    name: 'pce_memory_policy_apply',
    description:
      'Initialize memory system with policy configuration. Call once at session start before using other tools. Configures boundary rules, redaction patterns, and rate limits.',
    inputSchema: {
      type: 'object',
      properties: {
        yaml: { type: 'string', description: 'Policy YAML (uses default if omitted)' },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_observe',
    description:
      'Record a temporary observation with auto-expiry (default 30 days). Use for chat logs, tool outputs, file reads, API responses. Raw observations do not create durable claims; use pce_memory_distill + pce_memory_promote for durable memory. Auto-detects and redacts PII/secrets.',
    inputSchema: {
      type: 'object',
      properties: {
        source_type: { type: 'string', enum: ['chat', 'tool', 'file', 'http', 'system'] },
        source_id: { type: 'string' },
        content: { type: 'string' },
        boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        actor: { type: 'string' },
        tags: { type: 'array', items: { type: 'string' } },
        provenance: {
          type: 'object',
          properties: {
            at: { type: 'string', format: 'date-time' },
            actor: { type: 'string' },
            git: {
              type: 'object',
              properties: {
                commit: { type: 'string' },
                repo: { type: 'string' },
                url: { type: 'string' },
                files: { type: 'array', items: { type: 'string' } },
              },
            },
            url: { type: 'string' },
            note: { type: 'string' },
            signed: { type: 'boolean' },
          },
          required: ['at'],
        },
        ttl_days: { type: 'number', minimum: 1 },
        extract: {
          type: 'object',
          properties: {
            mode: {
              type: 'string',
              enum: ['noop'],
              description:
                'Reserved compatibility knob. noop preserves raw observations only; use pce_memory_distill + pce_memory_promote for durable memory.',
            },
          },
        },
      },
      required: ['source_type', 'content'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        observation_id: { type: 'string', description: 'Observation ID' },
        claim_ids: { type: 'array', items: { type: 'string' }, description: 'Extracted claim IDs' },
        effective_boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        content_stored: { type: 'boolean' },
        content_redacted: { type: 'boolean' },
        warnings: { type: 'array', items: { type: 'string' } },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: [
        'observation_id',
        'claim_ids',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_distill',
    description:
      'Create a promotion candidate from observations, claims, or an active context. Distill is the reviewable step between raw capture and durable memory.',
    inputSchema: {
      type: 'object',
      properties: {
        source_observation_ids: { type: 'array', items: { type: 'string' } },
        source_claim_ids: { type: 'array', items: { type: 'string' } },
        active_context_id: { type: 'string' },
        proposed_kind: { type: 'string', enum: [...CLAIM_KINDS] },
        proposed_scope: { type: 'string', enum: ['project', 'principle'] },
        proposed_memory_type: {
          type: 'string',
          enum: [...MEMORY_TYPES],
          description: 'Optional durable memory type. evidence is rejected for durable promotion.',
        },
        note: { type: 'string' },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        candidate_id: { type: 'string' },
        distilled_text: { type: 'string' },
        proposed_kind: { type: 'string', enum: [...CLAIM_KINDS] },
        proposed_scope: { type: 'string', enum: ['project', 'principle'] },
        proposed_memory_type: {
          type: 'string',
          enum: [...MEMORY_TYPES],
          description: 'Proposed memory type (nullable)',
        },
        proposed_boundary_class: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
        status: { type: 'string', enum: ['pending'] },
        invariant_check_results: { type: 'object' },
        policy_version: { type: 'string' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'candidate_id',
        'distilled_text',
        'proposed_kind',
        'proposed_scope',
        'proposed_boundary_class',
        'status',
        'invariant_check_results',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_promote',
    description:
      'Accept a pending promotion candidate and create a durable claim with mandatory provenance.',
    inputSchema: {
      type: 'object',
      properties: {
        candidate_id: { type: 'string' },
        provenance: {
          type: 'object',
          properties: {
            at: { type: 'string', format: 'date-time' },
            actor: { type: 'string' },
            git: {
              type: 'object',
              properties: {
                commit: { type: 'string' },
                repo: { type: 'string' },
                url: { type: 'string' },
                files: { type: 'array', items: { type: 'string' } },
              },
            },
            url: { type: 'string' },
            note: { type: 'string' },
            signed: { type: 'boolean' },
          },
          required: ['at'],
        },
        reviewers: { type: 'array', items: { type: 'string' } },
        review_note: { type: 'string' },
      },
      required: ['candidate_id', 'provenance'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        claim_id: { type: 'string' },
        target_layer: { type: 'string', enum: ['meso', 'macro'] },
        is_new: { type: 'boolean' },
        promoted_from: { type: 'string' },
        rollback_token: { type: 'string' },
        suggested_links: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              target: { type: 'string' },
              similarity: { type: 'number' },
              suggested_type: { type: 'string', enum: ['related'] },
            },
            required: ['target', 'similarity', 'suggested_type'],
          },
        },
        similar_existing: {
          type: 'array',
          description: 'Nearby active claims in the same scope with cosine similarity > 0.85',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              similarity: { type: 'number' },
              text_preview: { type: 'string' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'similarity', 'text_preview', 'created_at'],
          },
        },
        policy_version: { type: 'string' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'claim_id',
        'target_layer',
        'is_new',
        'promoted_from',
        'rollback_token',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_rollback',
    description:
      'Append-only rollback for a durable claim. Marks the claim as superseded and records rollback ancestry for audit.',
    inputSchema: {
      type: 'object',
      properties: {
        claim_id: { type: 'string' },
        reason: { type: 'string' },
        provenance: {
          type: 'object',
          properties: {
            at: { type: 'string', format: 'date-time' },
            actor: { type: 'string' },
            git: {
              type: 'object',
              properties: {
                commit: { type: 'string' },
                repo: { type: 'string' },
                url: { type: 'string' },
                files: { type: 'array', items: { type: 'string' } },
              },
            },
            url: { type: 'string' },
            note: { type: 'string' },
            signed: { type: 'boolean' },
          },
          required: ['at'],
        },
      },
      required: ['claim_id', 'reason', 'provenance'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        rollback_id: { type: 'string' },
        superseded_claim_id: { type: 'string' },
        blast_radius: { type: 'object' },
        policy_version: { type: 'string' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'rollback_id',
        'superseded_claim_id',
        'blast_radius',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_upsert',
    description:
      'Register a permanent knowledge claim (never auto-deleted). Use for verified decisions, resolved errors, architectural patterns. For project and principle scopes, provenance.at timestamp is required; session claims may omit provenance. Prefer over observe for long-term, validated knowledge. secret boundary_class is rejected by default; use observe for secret material.',
    inputSchema: {
      type: 'object',
      properties: {
        text: { type: 'string' },
        kind: { type: 'string', enum: [...CLAIM_KINDS] },
        scope: { type: 'string', enum: ['session', 'project', 'principle'] },
        boundary_class: {
          type: 'string',
          enum: ['public', 'internal', 'pii'],
          description:
            'Durable claims support public|internal|pii. secret is rejected by default; use pce_memory_observe for secret material.',
        },
        memory_type: {
          type: 'string',
          enum: [...MEMORY_TYPES],
          description:
            'Optional v2 memory taxonomy. Must match one of the domain MemoryType values.',
        },
        content_hash: {
          type: 'string',
          pattern: '^sha256:[0-9a-f]{64}$',
          description:
            'Optional. SHA256 hash of text for deduplication. Auto-generated if omitted; validated against text if provided.',
        },
        provenance: {
          type: 'object',
          description:
            'Optional for session scope. project and principle claims must include provenance.at.',
          properties: {
            at: {
              type: 'string',
              format: 'date-time',
              description: 'ISO8601 timestamp. Required for project and principle scopes.',
            },
            actor: { type: 'string' },
            git: {
              type: 'object',
              properties: {
                commit: { type: 'string' },
                repo: { type: 'string' },
                url: { type: 'string' },
                files: { type: 'array', items: { type: 'string' } },
              },
            },
            url: { type: 'string' },
            note: { type: 'string' },
            signed: { type: 'boolean' },
          },
        },
        entities: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              type: { type: 'string', enum: ['Actor', 'Artifact', 'Event', 'Concept'] },
              name: { type: 'string' },
              canonical_key: { type: 'string' },
              attrs: { type: 'object' },
            },
            required: ['id', 'type', 'name'],
          },
        },
        relations: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              src_id: { type: 'string' },
              dst_id: { type: 'string' },
              type: { type: 'string' },
              props: { type: 'object' },
              evidence_claim_id: { type: 'string' },
            },
            required: ['id', 'src_id', 'dst_id', 'type'],
          },
        },
      },
      required: ['text', 'kind', 'scope', 'boundary_class'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Claim ID' },
        is_new: { type: 'boolean', description: 'Whether this is a new claim' },
        content_hash: {
          type: 'string',
          description: 'SHA256 hash of text (auto-generated or provided)',
        },
        suggested_links: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              target: { type: 'string' },
              similarity: { type: 'number' },
              suggested_type: { type: 'string', enum: ['related'] },
            },
            required: ['target', 'similarity', 'suggested_type'],
          },
          description: 'Similarity-based related-link suggestions for newly created claims',
        },
        graph_memory: {
          type: 'object',
          properties: {
            entities: {
              type: 'object',
              properties: {
                success: { type: 'integer', minimum: 0 },
                failed: { type: 'integer', minimum: 0 },
              },
              required: ['success', 'failed'],
            },
            relations: {
              type: 'object',
              properties: {
                success: { type: 'integer', minimum: 0 },
                failed: { type: 'integer', minimum: 0 },
              },
              required: ['success', 'failed'],
            },
          },
          description: 'Graph memory operation results (optional)',
        },
        similar_existing: {
          type: 'array',
          description: 'Nearby active claims in the same scope with cosine similarity > 0.85',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              similarity: { type: 'number' },
              text_preview: { type: 'string' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'similarity', 'text_preview', 'created_at'],
          },
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'is_new', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_link_claims',
    description:
      'Create or update an explicit claim-to-claim link so activate can traverse connected knowledge.',
    inputSchema: {
      type: 'object',
      properties: {
        source_claim_id: { type: 'string' },
        target_claim_id: { type: 'string' },
        link_type: { type: 'string', enum: [...CLAIM_LINK_TYPES] },
        confidence: {
          type: 'number',
          minimum: 0,
          maximum: 1,
          description: 'Optional confidence override. Defaults to 1.0.',
        },
      },
      required: ['source_claim_id', 'target_claim_id', 'link_type'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string' },
        is_new: { type: 'boolean' },
        source_claim_id: { type: 'string' },
        target_claim_id: { type: 'string' },
        link_type: { type: 'string', enum: [...CLAIM_LINK_TYPES] },
        confidence: { type: 'number' },
        created_by: { type: 'string', enum: ['client', 'auto_similarity'] },
        policy_version: { type: 'string' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'id',
        'is_new',
        'source_claim_id',
        'target_claim_id',
        'link_type',
        'confidence',
        'created_by',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_activate',
    description:
      'Retrieve relevant knowledge for current task via hybrid search. Call before starting work to recall past decisions, patterns, and solutions. Returns ranked claims filtered by scope and boundary, plus optional maintenance_hints when policy-enabled.',
    inputSchema: {
      type: 'object',
      properties: {
        scope: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Pace layer scopes to search',
        },
        allow: {
          type: 'array',
          items: { type: 'string' },
          description:
            'Policy allow tags to filter claims (e.g., ["answer:task", "tool:*"] or ["*"] for all). These are NOT boundary_class names. Default policy: public=["*"], internal=["answer:task", "tool:*"]',
        },
        top_k: { type: 'integer', minimum: 1, maximum: 50, description: 'Max claims to return' },
        q: { type: 'string', description: 'Search query string (partial match)' },
        intent: {
          type: 'string',
          enum: [...ACTIVATE_INTENTS],
          description: 'Intent profile for retrieval planning',
        },
        kind_filter: {
          type: 'array',
          items: { type: 'string', enum: [...CLAIM_KINDS] },
          description: 'Optional claim kind filter applied before ranking',
        },
        memory_type_filter: {
          type: 'array',
          items: { type: 'string', enum: [...MEMORY_TYPES] },
          description: 'Optional memory_type filter applied before ranking',
        },
        cursor: { type: 'string', description: 'Pagination cursor' },
        include_meta: {
          type: 'boolean',
          description: 'Include metadata (evidence, etc.)',
          default: false,
        },
        include_observations: {
          type: 'boolean',
          description:
            'Also search transient observations for short-term recall and return them as micro-layer items.',
          default: false,
        },
        include_stale_tasks: {
          type: 'boolean',
          description:
            'Include stale working_state claims in activate results. Completed items remain excluded.',
          default: false,
        },
      },
      required: ['scope', 'allow'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        active_context_id: { type: 'string', description: 'Active context ID' },
        intent: {
          type: 'string',
          enum: [...ACTIVATE_INTENTS],
          description: 'Echoed intent when provided',
        },
        claims: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              claim: {
                type: 'object',
                description:
                  'Claim data with optional freshness metadata when a newer similar claim exists',
                properties: {
                  freshness: { type: 'string', enum: ['stale_candidate'] },
                  newer_similar: { type: 'string' },
                },
              },
              score: { type: 'number', description: 'Relevance score' },
              source_layer: {
                type: 'string',
                enum: ['micro', 'meso', 'macro'],
                description: 'Layer derived from claim scope',
              },
              source: {
                type: 'string',
                enum: ['search', 'observation', 'claim_link'],
                description: 'How the item entered the activate result set',
              },
              link: {
                type: 'object',
                properties: {
                  id: { type: 'string' },
                  via_claim_id: { type: 'string' },
                  link_type: { type: 'string', enum: [...CLAIM_LINK_TYPES] },
                  confidence: { type: 'number' },
                },
                required: ['id', 'via_claim_id', 'link_type', 'confidence'],
              },
              rank: { type: 'integer', minimum: 1, description: 'Returned rank' },
              score_breakdown: {
                type: 'object',
                description: 'Hybrid and rerank score breakdown',
              },
              selection_reason: {
                type: 'string',
                description: 'Compact explanation of why the item was selected',
              },
              evidences: { type: 'array', items: { type: 'object' }, description: 'Evidence list' },
            },
          },
          description: 'Scored claims with optional evidences',
        },
        claims_count: { type: 'integer', minimum: 0, description: 'Number of claims returned' },
        next_cursor: { type: 'string', description: 'Pagination cursor for next page' },
        has_more: { type: 'boolean', description: 'Whether more results exist' },
        maintenance_hints: {
          type: 'object',
          description:
            'Optional knowledge maintenance signals derived from retrieved claims and store health.',
          properties: {
            similar_pairs: {
              type: 'array',
              items: {
                type: 'object',
                properties: {
                  a: { type: 'string', description: 'First similar claim id' },
                  b: { type: 'string', description: 'Second similar claim id' },
                  similarity: { type: 'number', description: 'Cosine similarity score' },
                  suggestion: {
                    type: 'string',
                    enum: ['consider_consolidation'],
                    description: 'Suggested maintenance action',
                  },
                },
              },
            },
            stale_candidates: {
              type: 'array',
              items: {
                type: 'object',
                properties: {
                  id: { type: 'string', description: 'Stale claim id' },
                  last_retrieved_at: {
                    type: 'null',
                    description: 'Always null when retrieval_count is zero',
                  },
                  days_since_created: {
                    type: 'integer',
                    minimum: 0,
                    description: 'Age of the claim in days',
                  },
                },
              },
            },
            unprocessed_observations: {
              type: 'integer',
              minimum: 0,
              description: 'Count of non-expired raw observations still carrying content',
            },
            high_retrieval_no_feedback: {
              type: 'array',
              items: {
                type: 'object',
                properties: {
                  id: { type: 'string', description: 'Frequently retrieved claim id' },
                  retrieval_count: {
                    type: 'integer',
                    minimum: 0,
                    description: 'Observed retrieval count from active context items',
                  },
                  feedback_count: {
                    type: 'integer',
                    minimum: 0,
                    description: 'Feedback event count for the claim',
                  },
                },
              },
            },
          },
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: [
        'active_context_id',
        'claims',
        'claims_count',
        'has_more',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_boundary_validate',
    description:
      'Validate and redact sensitive content before outputting to user. Checks for PII, secrets, and boundary policy violations. Returns sanitized payload safe for external use.',
    inputSchema: {
      type: 'object',
      properties: {
        payload: { type: 'string', description: 'Content to validate and potentially redact' },
        allow: {
          type: 'array',
          items: { type: 'string' },
          description:
            'Policy allow tags for boundary check (e.g., ["answer:task"] or ["*"]). NOT boundary_class names.',
        },
        scope: {
          type: 'string',
          enum: ['session', 'project', 'principle'],
          description: 'Pace layer scope for validation',
        },
      },
      required: ['payload'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        allowed: { type: 'boolean', description: 'Whether the payload is allowed' },
        redacted: { type: 'string', description: 'Redacted payload' },
        violations: {
          type: 'array',
          items: { type: 'string' },
          description: 'List of boundary violations',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['allowed', 'redacted', 'policy_version', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_feedback',
    description:
      'Report knowledge quality after using activated claims. Send helpful when knowledge solved the problem, harmful if it caused errors, outdated if info was stale, duplicate if redundant, or completed to close a working_state claim.',
    inputSchema: {
      type: 'object',
      properties: {
        claim_id: { type: 'string' },
        signal: {
          type: 'string',
          enum: ['helpful', 'harmful', 'outdated', 'duplicate', 'completed'],
        },
        score: { type: 'number', minimum: -1, maximum: 1 },
      },
      required: ['claim_id', 'signal'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Feedback ID' },
        claim_id: { type: 'string', description: 'Target claim ID' },
        signal: {
          type: 'string',
          enum: ['helpful', 'harmful', 'outdated', 'duplicate', 'completed'],
          description: 'Feedback signal',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'claim_id', 'signal', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_state',
    description: 'Get current state machine status (Uninitialized/PolicyApplied/HasClaims/Ready)',
    inputSchema: {
      type: 'object',
      properties: {
        debug: {
          type: 'boolean',
          description: 'Debug mode: include runtime_state details (default: false)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        claim_count: { type: 'integer', minimum: 0, description: 'Number of claims' },
        active_context_id: { type: 'string', description: 'Current active context ID' },
        runtime_state: { type: 'object', description: 'Runtime state details (debug mode)' },
        layer_scope: { type: 'object', description: 'Layer/scope state (debug mode)' },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['state', 'policy_version', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_health',
    description:
      'Get knowledge base health report. Returns claim statistics, confidence distribution, feedback summary, utility distribution, and activation coverage. No parameters required.',
    inputSchema: {
      type: 'object',
      properties: {},
    },
    outputSchema: {
      type: 'object',
      properties: {
        total_claims: { type: 'integer', minimum: 0, description: 'Total number of claims' },
        by_kind: {
          type: 'object',
          description: `Claim count by kind (${CLAIM_KINDS.join('/')})`,
        },
        by_scope: {
          type: 'object',
          description: 'Claim count by scope (session/project/principle)',
        },
        confidence_bands: {
          type: 'object',
          properties: {
            high: { type: 'integer' },
            medium: { type: 'integer' },
            low: { type: 'integer' },
          },
          description: 'Claims grouped by confidence level',
        },
        last_positive_feedback_age: {
          type: 'object',
          properties: {
            recent_30d: { type: 'integer' },
            stale_90d: { type: 'integer' },
            dormant: { type: 'integer' },
          },
        },
        duplicate_feedback_rate: {
          type: 'number',
          description: 'Rate of duplicate feedback signals',
        },
        never_activated_ratio: {
          type: 'object',
          properties: {
            overall: { type: 'number' },
            by_age_bucket: { type: 'object' },
          },
        },
        utility_distribution: {
          type: 'object',
          properties: {
            mean: { type: 'number' },
            median: { type: 'number' },
            p10: { type: 'number' },
            p90: { type: 'number' },
          },
        },
        feedback_summary: { type: 'object', description: 'Feedback count by signal type' },
        policy_version: { type: 'string' },
        state: { type: 'string', enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'] },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'total_claims',
        'by_kind',
        'by_scope',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  // ========== Graph Memory Tools ==========
  {
    name: 'pce_memory_upsert_entity',
    description: 'Register an entity in graph memory (Actor/Artifact/Event/Concept)',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        name: { type: 'string', description: 'Entity name' },
        canonical_key: {
          type: 'string',
          description: 'Canonical key (optional, for deduplication)',
        },
        attrs: { type: 'object', description: 'Additional attributes (optional)' },
      },
      required: ['id', 'type', 'name'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        name: { type: 'string', description: 'Entity name' },
        canonical_key: { type: 'string', description: 'Canonical key (if set)' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['id', 'type', 'name', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_upsert_relation',
    description: 'Register a relation between entities in graph memory',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type (e.g., KNOWS, USES, DEPENDS_ON)' },
        props: { type: 'object', description: 'Additional relation properties (optional)' },
        evidence_claim_id: {
          type: 'string',
          description: 'Claim ID as evidence for this relation (optional)',
        },
      },
      required: ['id', 'src_id', 'dst_id', 'type'],
    },
    outputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type' },
        evidence_claim_id: { type: 'string', description: 'Evidence claim ID (if set)' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: [
        'id',
        'src_id',
        'dst_id',
        'type',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_query_entity',
    description:
      'Query entities from graph memory. At least one filter is required: id, type, canonical_key, or claim_id. Use limit to control result count.',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Entity ID (exact match)' },
        type: {
          type: 'string',
          enum: ['Actor', 'Artifact', 'Event', 'Concept'],
          description: 'Entity type',
        },
        canonical_key: { type: 'string', description: 'Canonical key (exact match)' },
        claim_id: { type: 'string', description: 'Claim ID to find linked entities' },
        limit: {
          type: 'integer',
          minimum: 1,
          maximum: 100,
          description: 'Max results (default: 50)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        entities: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              type: { type: 'string', enum: ['Actor', 'Artifact', 'Event', 'Concept'] },
              name: { type: 'string' },
              canonical_key: { type: 'string' },
              attrs: { type: 'object' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'type', 'name'],
          },
          description: 'Matching entities',
        },
        count: { type: 'integer', minimum: 0, description: 'Number of entities returned' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['entities', 'count', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  {
    name: 'pce_memory_query_relation',
    description:
      'Query relations from graph memory. At least one filter is required: id, src_id, dst_id, type, or evidence_claim_id. Use limit to control result count.',
    inputSchema: {
      type: 'object',
      properties: {
        id: { type: 'string', description: 'Relation ID (exact match)' },
        src_id: { type: 'string', description: 'Source entity ID' },
        dst_id: { type: 'string', description: 'Target entity ID' },
        type: { type: 'string', description: 'Relation type (e.g., TAGGED, KNOWS)' },
        evidence_claim_id: { type: 'string', description: 'Evidence claim ID' },
        limit: {
          type: 'integer',
          minimum: 1,
          maximum: 100,
          description: 'Max results (default: 50)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        relations: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              id: { type: 'string' },
              src_id: { type: 'string' },
              dst_id: { type: 'string' },
              type: { type: 'string' },
              evidence_claim_id: { type: 'string' },
              props: { type: 'object' },
              created_at: { type: 'string', format: 'date-time' },
            },
            required: ['id', 'src_id', 'dst_id', 'type'],
          },
          description: 'Matching relations',
        },
        count: { type: 'integer', minimum: 0, description: 'Number of relations returned' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
          description: 'Current state machine state',
        },
        request_id: { type: 'string', description: 'Unique request identifier' },
        trace_id: { type: 'string', description: 'Trace identifier for debugging' },
      },
      required: ['relations', 'count', 'policy_version', 'state', 'request_id', 'trace_id'],
    },
  },
  // ========== Sync Tools (Issue #18) ==========
  {
    name: 'pce_memory_sync_push',
    description:
      'Export local claims/entities/relations to .pce-shared/ directory for Git-based CRDT sync',
    inputSchema: {
      type: 'object',
      properties: {
        target_dir: {
          type: 'string',
          description: 'Target directory path (default: .pce-shared at Git root if available)',
        },
        scope_filter: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Filter by scope (default: ["project", "principle"])',
        },
        boundary_filter: {
          type: 'array',
          items: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
          description:
            'Filter by boundary_class (default: ["public", "internal"], secret is always excluded)',
        },
        since: {
          type: 'string',
          format: 'date-time',
          description: 'Export only claims created/updated after this time (ISO8601)',
        },
        include_entities: {
          type: 'boolean',
          description: 'Include entities in export (default: true)',
        },
        include_relations: {
          type: 'boolean',
          description: 'Include relations in export (default: true)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        exported: {
          type: 'object',
          properties: {
            claims: { type: 'integer', minimum: 0 },
            entities: { type: 'integer', minimum: 0 },
            relations: { type: 'integer', minimum: 0 },
          },
          required: ['claims', 'entities', 'relations'],
        },
        target_dir: { type: 'string', description: 'Actual target directory path' },
        manifest_updated: { type: 'boolean', description: 'Whether manifest.json was updated' },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'exported',
        'target_dir',
        'manifest_updated',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  {
    name: 'pce_memory_sync_pull',
    description:
      'Import claims/entities/relations from .pce-shared/ directory with CRDT merge strategy',
    inputSchema: {
      type: 'object',
      properties: {
        source_dir: {
          type: 'string',
          description: 'Source directory path (default: .pce-shared at Git root if available)',
        },
        scope_filter: {
          type: 'array',
          items: { type: 'string', enum: ['session', 'project', 'principle'] },
          description: 'Filter by scope (default: all)',
        },
        boundary_filter: {
          type: 'array',
          items: { type: 'string', enum: ['public', 'internal', 'pii', 'secret'] },
          description: 'Filter by boundary_class (default: all except secret)',
        },
        dry_run: {
          type: 'boolean',
          description: 'Preview changes without applying (default: false)',
        },
        since: {
          type: 'string',
          format: 'date-time',
          description:
            'Incremental import: only import claims with provenance.at >= since (ISO8601)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        imported: {
          type: 'object',
          properties: {
            claims: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
                upgraded_boundary: { type: 'integer', minimum: 0 },
                skipped_by_since: {
                  type: 'integer',
                  minimum: 0,
                  description: 'Skipped due to since filter',
                },
              },
              required: ['new', 'skipped_duplicate', 'upgraded_boundary', 'skipped_by_since'],
            },
            entities: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
              },
              required: ['new', 'skipped_duplicate'],
            },
            relations: {
              type: 'object',
              properties: {
                new: { type: 'integer', minimum: 0 },
                skipped_duplicate: { type: 'integer', minimum: 0 },
              },
              required: ['new', 'skipped_duplicate'],
            },
          },
          required: ['claims', 'entities', 'relations'],
        },
        validation_errors: {
          type: 'array',
          items: {
            type: 'object',
            properties: {
              file: { type: 'string' },
              error: { type: 'string' },
            },
            required: ['file', 'error'],
          },
          description: 'List of validation errors encountered',
        },
        dry_run: { type: 'boolean', description: 'Whether this was a dry run' },
        manifest_updated: {
          type: 'boolean',
          description: 'Whether manifest.json was updated with last_pull_at',
        },
        policy_version: { type: 'string', description: 'Policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'imported',
        'validation_errors',
        'dry_run',
        'manifest_updated',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
  // Phase 2: sync.status
  {
    name: 'pce_memory_sync_status',
    description: 'Get sync directory status including manifest, file counts, and validation state',
    inputSchema: {
      type: 'object',
      properties: {
        target_dir: {
          type: 'string',
          description: 'Target directory path (default: .pce-shared at Git root if available)',
        },
      },
    },
    outputSchema: {
      type: 'object',
      properties: {
        exists: { type: 'boolean', description: 'Whether sync directory exists' },
        manifest: {
          type: 'object',
          properties: {
            version: { type: 'string' },
            pce_memory_version: { type: 'string' },
            last_push_at: { type: 'string', format: 'date-time' },
            last_push_policy_version: { type: 'string' },
            last_pull_at: { type: 'string', format: 'date-time' },
          },
          description: 'Manifest content (if exists)',
        },
        files: {
          type: 'object',
          properties: {
            claims: { type: 'integer', minimum: 0 },
            entities: { type: 'integer', minimum: 0 },
            relations: { type: 'integer', minimum: 0 },
          },
          required: ['claims', 'entities', 'relations'],
          description: 'File counts by type',
        },
        validation: {
          type: 'object',
          properties: {
            isValid: { type: 'boolean' },
            errors: { type: 'array', items: { type: 'string' } },
          },
          required: ['isValid', 'errors'],
          description: 'Validation status',
        },
        target_dir: { type: 'string', description: 'Actual target directory path' },
        policy_version: { type: 'string', description: 'Current policy version' },
        state: {
          type: 'string',
          enum: ['Uninitialized', 'PolicyApplied', 'HasClaims', 'Ready'],
        },
        request_id: { type: 'string' },
        trace_id: { type: 'string' },
      },
      required: [
        'exists',
        'files',
        'validation',
        'target_dir',
        'policy_version',
        'state',
        'request_id',
        'trace_id',
      ],
    },
  },
];

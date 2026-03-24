# Local LLM Effectiveness Report

Generated: 2026-03-24T22:05:47.094Z

## Configuration

- Ollama endpoint: `http://localhost:11434/v1/chat/completions`
- Ollama models endpoint: `http://localhost:11434/v1/models`
- Model: `qwen3.5:122b-a10b`
- Max tokens: `1500`
- JSON retry max tokens: `3000`
- Reasoning effort: `none`
- Temperature: `0`
- Target file: `apps/pce-memory/src/store/hybridSearch.ts`
- MCP server: `apps/pce-memory/dist/index.js`

## Preflight

- Available models: `qwen3.5:9b`, `qwen3.5:35b`, `qwen3.5:122b-a10b`, `bge-m3:latest`, `qwen3-next:80b-a3b-instruct-q4_K_M`, `qwen3:30b-a3b`, `qwen3-coder-next:latest`, `claude-sonnet-4-5-20250929:latest`, `qwen3-coder:30b`, `gpt-oss:120b`

## Experiment 1: Task Continuity

- WITH-MEMORY verdict: `specific_recall`
- WITH-MEMORY slug recall: 3/3
- WITH-MEMORY invalid reasons: none
- WITHOUT-MEMORY verdict: `generic_or_no_context`
- WITHOUT-MEMORY slug recall: 0/3
- WITHOUT-MEMORY invalid reasons: none

### WITH-MEMORY recovered slugs

- `prevent-sql-injection-via-embedding-literal`
- `optimize-paginated-query-performance`
- `enforce-embedding-magnitude-check-completion`

### WITHOUT-MEMORY missing slugs

- `prevent-sql-injection-via-embedding-literal`
- `optimize-paginated-query-performance`
- `enforce-embedding-magnitude-check-completion`

### WITH-MEMORY Phase B answer

```text
{
  "status": "ok",
  "improvements": [
    {
      "slug": "optimize-paginated-query-performance",
      "explanation": "The code fetches an excessive number of results when a cursor is present, causing high memory usage and latency.",
      "evidence": [
        "const fetchLimit = cursor ? Number.MAX_SAFE_INTEGER : limit + 1",
        "await hybridSearchWithScores(scopes, Number.MAX_SAFE_INTEGER, undefined, config)",
        "const cursorIndex = allResults.findIndex((r) => r.claim.id === cursor)"
      ]
    },
    {
      "slug": "prevent-sql-injection-via-embedding-literal",
      "explanation": "SQL queries are constructed by interpolating embedding literals directly, which bypasses standard parameterization and increases injection risk.",
      "evidence": [
        "const embeddingLiteral = `[${[...queryEmbedding].join(',')}]`",
        "const embeddingLiteral = `[${embedding.join(',')}]`",
        "VALUES ($1, ${embeddingLiteral}::DOUBLE[], $2)"
      ]
    },
    {
      "slug": "enforce-embedding-magnitude-check-completion",
      "explanation": "The validation logic for embedding magnitude appears incomplete as the provided code snippet cuts off before the error throw statement.",
      "evidence": [
        "if (Math.abs(v) > MAX_EMBEDDING_MAGNITUDE) {",
        "validateEmbedding(queryEmbedding)",
        "validateEmbedding(embedding)"
      ]
    }
  ]
}
```

### WITHOUT-MEMORY Phase B answer

```text
{"status":"no_context","improvements":[]}
```

## Experiment 2: Design Decision Recall

- WITH-MEMORY verdict: `specific_recall`
- WITH-MEMORY decision recall: 3/3
- WITH-MEMORY invalid reasons: none
- WITHOUT-MEMORY verdict: `generic_or_no_context`
- WITHOUT-MEMORY decision recall: 0/3
- WITHOUT-MEMORY invalid reasons: none

### WITH-MEMORY recovered decision ids

- `retrieval-alpha-0-65-vector-bias`
- `retrieval-threshold-0-15-noise-gate`
- `retrieval-candidate-pools-48-96`

### WITHOUT-MEMORY missing decision ids

- `retrieval-alpha-0-65-vector-bias`
- `retrieval-threshold-0-15-noise-gate`
- `retrieval-candidate-pools-48-96`

### WITH-MEMORY answer

```text
{
  "status": "ok",
  "decisions": [
    {
      "id": "retrieval-alpha-0-65-vector-bias",
      "summary": "The retrieval pipeline fuses text and vector scores with ALPHA=0.65, intentionally biasing ranking toward vector search results.",
      "params": [
        "ALPHA=0.65"
      ]
    },
    {
      "id": "retrieval-candidate-pools-48-96",
      "summary": "The retrieval pipeline expands recall with K_TEXT=48 and K_VEC=96 candidate pools before merge and reranking.",
      "params": [
        "K_TEXT=48",
        "K_VEC=96"
      ]
    },
    {
      "id": "retrieval-threshold-0-15-noise-gate",
      "summary": "The retrieval pipeline applies THRESHOLD=0.15 to suppress low-signal candidates before the final result set is returned.",
      "params": [
        "THRESHOLD=0.15"
      ]
    }
  ]
}
```

### WITHOUT-MEMORY answer

```text
{"status":"no_context","decisions":[]}
```

## Takeaway

- Experiment 1 shows whether persisted memory can recover prior session findings instead of forcing the model to answer from scratch.
- Experiment 2 shows whether explicit architectural decisions are recalled with concrete ids and parameter values once they are stored in pce-memory.

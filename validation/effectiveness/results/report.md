# Local LLM Effectiveness Report

Generated: 2026-03-24T21:40:44.147Z

## Configuration

- Ollama endpoint: `http://localhost:11434/v1/chat/completions`
- Ollama models endpoint: `http://localhost:11434/v1/models`
- Model: `qwen3.5:122b-a10b`
- Max tokens: `1500`
- Temperature: `0`
- Target file: `apps/pce-memory/src/store/hybridSearch.ts`
- MCP server: `apps/pce-memory/dist/index.js`

## Preflight

- Available models: `qwen3.5:9b`, `qwen3.5:35b`, `qwen3.5:122b-a10b`, `bge-m3:latest`, `qwen3-next:80b-a3b-instruct-q4_K_M`, `qwen3:30b-a3b`, `qwen3-coder-next:latest`, `claude-sonnet-4-5-20250929:latest`, `qwen3-coder:30b`, `gpt-oss:120b`

## Experiment 1: Task Continuity

- WITH-MEMORY verdict: `specific_recall`
- WITH-MEMORY slug recall: 3/3
- WITHOUT-MEMORY verdict: `generic_or_no_context`
- WITHOUT-MEMORY slug recall: 0/3

### WITH-MEMORY recovered slugs

- `memory-inefficiency-in-pagination`
- `hardcoded-retrieval-limits`
- `sql-injection-risk-in-vector-literals`

### WITHOUT-MEMORY missing slugs

- `memory-inefficiency-in-pagination`
- `hardcoded-retrieval-limits`
- `sql-injection-risk-in-vector-literals`

### WITH-MEMORY Phase B answer

```text
Thinking Process:

1.  **Analyze the Request:**
    *   Task: Answer a question about previous session improvements for `hybridSearch.ts`.
    *   Constraint: Use the provided simulated MCP tool result as authoritative prior-session memory. Do not invent details absent from it.
    *   Output: Exact improvement slugs and a short explanation for each.
    *   Input: A "Draft analysis" containing a simulated MCP tool result (`pce_memory_activate`) with three claims regarding `hybridSearch.ts`.

2.  **Analyze the Tool Result (Memory):**
    *   **Claim 1:**
        *   `improvement_id`: `memory-inefficiency-in-pagination`
        *   `title`: `Memory Inefficiency in Pagination`
        *   `why`: `Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.`
        *   `evidence`: Contains a JSON schema placeholder (`"slug":"kebab-case-id"`, `"title":"short title"`, etc.), suggesting the specific details aren't fully populated in the evidence field, but the `improvement_id` is explicit.
    *   **Claim 2:**
        *   `improvement_id`: `hardcoded-retrieval-limits`
        *   `title`: `Hardcoded Retrieval Limits`
        *   `why`: `Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.`
        *   `evidence`: `ALPHA, THRESHOLD, K_TEXT`
    *   **Claim 3:**
        *   `improvement_id`: `sql-injection-risk-in-vector-literals`
        *   `title`: `SQL Injection Risk in Vector Literals`
        *   `why`: `Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.`
        *   `evidence`: `K_TEXT, K_VEC, DEFAULT_CRITIC_SCORE`

3.  **Determine Output Format:**
    *   List exact improvement slugs (using `improvement_id` as the slug identifier based on the claim structure).
    *   Provide a short explanation for each.
    *   Adhere strictly to the provided text (do not invent details).

4.  **Drafting the Content:**
    *   **Slug 1:** `memory-inefficiency-in-pagination`
        *   **Explanation:** Memory Inefficiency in Pagination (Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts).
    *   **Slug 2:** `hardcoded-retrieval-limits`
        *   **Explanation:** Hardcoded Retrieval Limits (Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts).
    *   **Slug 3:** `sql-injection-risk-in-vector-literals`
        *   **Explanation:** SQL Injection Risk in Vector Literals (Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts).

5.  **Refining for Constraints:**
    *   The prompt asks for "exact improvement slugs". The `improvement_id` field is the most logical candidate for the slug.
    *   The prompt asks for a "short explanation". The `title` combined with the `why` field provides the only available explanation without hallucination.
    *   Ensure no commentary about the conversion step is included.

6.  **Final Polish:**
    *   Present as a clean list.

    *   *Self-Correction on Claim 1 Evidence:* The evidence in Claim 1 contains `"slug":"kebab-case-id"`. However, the `improvement_id` is `memory-inefficiency-in-pagination`. Given the evidence JSON looks like a template (`"title":"short title"`), the `improvement_id` is the reliable identifier for the improvement itself. I will use `improvement_id` as the slug.

    *   *Explanation:* Since the `why` field is identical and generic ("Inferred from the model reasoning trace..."), I will use the `title` to contextualize the explanation while citing the source of the inference.

    *   *Final check:* Does this violate "Do not invent details"? No, I am using the `title` and `why` exactly as provided.

    *   *Formatting:* Bullet points or numbered list.

    *   *Wait, one more check:* The prompt says "Convert the draft analysis into the direct final answer only." The draft analysis *is* the tool result provided in the prompt text under "Draft analysis:". I need to output the answer based on that.

    *   *Wait, looking at Claim 1 evidence again:* `evidence=apps/pce-memory/src/store/hybridSearch.ts, {"improvements":[{"slug":"kebab-case-id","title":"short title","why":"one-sentence rationale","evidence":["identifier1","identifier2"]}]}, ALPHA`. This looks like the evidence *field* contains a schema definition, not the actual improvement data. However, the `improvement_id` in the claim text is `memory-inefficiency-in-pagination`. I will proceed with `improvement_id` as the slug.

    *   *Final Decision:* List the three `improvement_id`s and their corresponding `title` + `why`.

    *   *Wait, constraint:* "Do not include commentary about the conversion step." Just the answer.

    *   *Final Output Structure:*
        *   Slug: [id]
        *   Explanation: [title] - [why]

    *   Let's make it concise.

    *   **Improvement 1:**
        *   Slug: `memory-inefficiency-in-pagination`
        *   Explanation: Memory Inefficiency in Pagination. Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.
    *   **Improvement 2:**
        *   Slug: `hardcoded-retrieval-limits`
        *   Explanation: Hardcoded Retrieval Limits. Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.
    *   **Improvement 3:**
        *   Slug: `sql-injection-risk-in-vector-literals`
        *   Explanation: SQL Injection Risk in Vector Literals. Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts.

    *   Actually, I can combine title and why for brevity. "Memory Inefficiency in Pagination (Inferred from the model reasoning trace for apps/pce-memory/src/store/hybridSearch.ts)."

    *   Let's ensure I don't miss anything. The prompt asks for "exact improvement slugs". I will use the `improvement_id` values.

    *   Ready to write.

    *   Wait, I need to check if `kebab-case-id` in Claim
```

### WITHOUT-MEMORY Phase B answer

```text
I do not have access to any previous session context. This appears to be the beginning of our current conversation, and no information regarding `hybridSearch.ts` or previously identified improvement slugs has been provided here. Consequently, I cannot list the improvements or explanations you are asking for.
```

## Experiment 2: Design Decision Recall

- WITH-MEMORY verdict: `specific_recall`
- WITH-MEMORY decision recall: 3/3
- WITHOUT-MEMORY verdict: `generic_or_no_context`
- WITHOUT-MEMORY decision recall: 0/3

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
Based on the retrieved memory, the following architectural decisions have been made regarding the retrieval pipeline:

1.  **Decision ID:** `retrieval-alpha-0-65-vector-bias`
    *   **Parameter:** `ALPHA=0.65`
    *   **Description:** The pipeline fuses text and vector scores with this alpha value, intentionally biasing ranking toward vector search results.

2.  **Decision ID:** `retrieval-candidate-pools-48-96`
    *   **Parameters:** `K_TEXT=48`, `K_VEC=96`
    *   **Description:** The pipeline expands recall using these candidate pool sizes before the merge and reranking stage.

3.  **Decision ID:** `retrieval-threshold-0-15-noise-gate`
    *   **Parameter:** `THRESHOLD=0.15`
    *   **Description:** The pipeline applies this threshold to suppress low-signal candidates before the final result set is returned.
```

### WITHOUT-MEMORY answer

```text
Based on the current conversation, there is no prior architectural context or information regarding a retrieval pipeline available. Consequently, I cannot provide specific decision IDs or concrete parameter values.

If you have documentation, logs, or previous discussion points you would like me to review, please share them, and I can analyze the information provided.
```

## Takeaway

- Experiment 1 shows whether persisted memory can recover prior session findings instead of forcing the model to answer from scratch.
- Experiment 2 shows whether explicit architectural decisions are recalled with concrete ids and parameter values once they are stored in pce-memory.

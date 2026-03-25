# LLM Entity Extraction Validation Report

Generated at: 2026-03-25T04:41:23.344Z

Runtime: qwen3.5:9b @ http://127.0.0.1:11434

## Assumptions

- Entity precision/recall uses a manually curated gold set with alias matching so hyphenation and snake_case variants are treated as the same concept.
- Relation quality scores unordered meaningful pairs; relation type histograms are reported separately to show whether the LLM emits typed edges instead of only generic co-occurrence.
- Query expansion compares three retrieval conditions: no linked entities, only LLM-extracted entities/relations, and an oracle manual-entity upper bound with shared topical seeds.

## Test 1: Extraction Quality

| Extractor | Total entities | Matched | Noise | Precision | Recall |
| --- | ---: | ---: | ---: | ---: | ---: |
| Pattern NLP | 11 | 9 | 2 | 0.818 | 0.214 |
| LLM | 22 | 20 | 2 | 0.909 | 0.476 |

Precision delta (LLM - Pattern): 0.091

Recall delta (LLM - Pattern): 0.262

## Test 2: Noise Rate

| Extractor | Noise entities | Total entities | Noise rate | Target < 0.2 |
| --- | ---: | ---: | ---: | --- |
| Pattern NLP | 2 | 11 | 0.182 | true |
| LLM | 2 | 22 | 0.091 | true |

LLM better than pattern: true

## Test 3: Relation Quality

| Extractor | Total relations | Matched pairs | Precision | Recall | Meaningful relations | Meaningful rate |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Pattern NLP | 3 | 1 | 0.333 | 0.034 | 0 | 0 |
| LLM | 17 | 11 | 0.647 | 0.379 | 13 | 0.765 |

Pattern relation types: CO_OCCURS: 3

LLM relation types: CONFIGURES: 6, USES: 5, RELATES_TO: 4, DEPENDS_ON: 2

LLM has meaningful relations: true

- Pattern NLP relations are synthetic co-occurs edges between all extracted entities in the same claim.
- LLM relation quality improves only when the extractor emits typed edges that land on the gold relation pairs.

## Test 4: Query Expansion Impact

| Query | P@3 No Entities | P@3 LLM Entities | P@3 Manual Entities | LLM Hits |
| --- | ---: | ---: | ---: | ---: |
| Authentication | 0 | 0 | 0.667 | 0/2 |
| Retrieval | 0.333 | 0.333 | 0.667 | 1/2 |
| Policy | 0.333 | 0.667 | 0.667 | 2/2 |
| Synchronization | 0 | 0 | 0.667 | 0/2 |
| Caching | 0.333 | 0.333 | 0.667 | 1/2 |

Average P@3 without entities: 0.2

Average P@3 with LLM entities: 0.267

Average P@3 with manual entities: 0.667

- The manual-entity arm adds one shared topical seed entity per claim cluster as an oracle upper bound for query expansion.
- The LLM arm uses only entities and relations produced by the real Ollama-backed extractor on the claim text itself.
- All three retrieval arms reuse the same deterministic local embedding service so score differences come from entity graph coverage, not embedding drift.

## Test 5: Latency

Target per claim: < 3000ms

Average: 4607.225ms

P50: 4985.872ms

P95: 5003.3ms

Max: 5003.3ms

Meets target: false

Over-target claims: claim_1, claim_2, claim_3, claim_4, claim_5, claim_6, claim_7, claim_8, claim_9, claim_10

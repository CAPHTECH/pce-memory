# Retrieval Precision Experiments

Benchmarks captured on 2026-03-25 from the targeted retrieval experiments in:

- `apps/pce-memory/test/retrieval-mmr-experiment.test.ts`
- `apps/pce-memory/test/retrieval-query-expansion-experiment.test.ts`
- `apps/pce-memory/test/retrieval-feedback-boost-experiment.test.ts`

Metrics:

- `P@3`: relevant claims in top 3 divided by 3
- `Recall@3`: relevant claims recovered in top 3 divided by total relevant claims
- `Diversity@3`: unique scenario clusters represented in top 3
- `Latency`: average `hybridSearchWithScores` runtime across 12 repeated runs in the benchmark harness

## Idea 1: MMR diversification

Scenario: duplicate-heavy authentication corpus where one JWT-rotation cluster crowds out broader relevant coverage.

| Variant |  P@3 | Recall@3 | Diversity@3 | Avg latency (ms) |
| ------- | ---: | -------: | ----------: | ---------------: |
| Before  | 0.33 |     0.33 |           1 |            10.19 |
| After   | 0.67 |     0.67 |           2 |             8.52 |

Result: MMR broke the all-duplicates top-3 pattern and recovered an additional relevant cluster without adding latency.

## Idea 2: Query expansion via entity graph

Scenario: the query is `authentication`, but the relevant claims only mention `JWT`, `Session`, and `Refresh Token`; the graph already links those entities.

| Variant |  P@3 | Recall@3 | Diversity@3 | Avg latency (ms) |
| ------- | ---: | -------: | ----------: | ---------------: |
| Before  | 0.00 |     0.00 |           0 |             1.93 |
| After   | 1.00 |     1.00 |           3 |             5.23 |

Result: one-hop graph expansion closed the lexical alias gap completely in this scenario and surfaced all three relevant claims.

## Idea 5: Feedback-loop scoring boost

Scenario: text-only retrieval where critic-heavy but repeatedly harmful rollback checklists beat repeatedly helpful ones unless feedback gets an explicit multiplier.

| Variant |  P@3 | Recall@3 | Diversity@3 | Avg latency (ms) |
| ------- | ---: | -------: | ----------: | ---------------: |
| Before  | 0.00 |     0.00 |           3 |             1.96 |
| After   | 1.00 |     1.00 |           3 |             7.12 |

Result: explicit feedback multipliers made stored helpful/harmful judgments matter in ordinary text-only retrieval instead of only in rerank-dependent paths.

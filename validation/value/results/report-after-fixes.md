# pce-memory Internal Validation Report

Generated: 2026-03-25T01:18:38.661Z

## Experiment 1: Search Precision

Average Precision@3: **0.9333**
Average NDCG@3: **0.9838**

| Query | Precision@3 | NDCG@3 | Actual top-3 |
| --- | ---: | ---: | --- |
| `policy_check_norm_over_task` | 0.6667 | 0.9468 | `clm_f4498ca6`, `clm_d16b2ffe`, `clm_f8822f6f` |
| `resume_task_working_state_over_norm` | 1 | 1 | `clm_c7046bab`, `clm_ad39c4bd`, `clm_d182a3ea` |
| `kind_filter_is_hard_filter` | 1 | 0.9721 | `clm_9e308567`, `clm_56863c51`, `clm_a12e3bf1` |
| `memory_type_filter_is_hard_filter` | 1 | 1 | `clm_0dda6e3c`, `clm_33685198`, `clm_4c20fb7d` |
| `authentication_query_avoids_caching_noise` | 1 | 1 | `clm_a151bf1a`, `clm_9ca87b89`, `clm_cfd673f2` |

## Experiment 2: Noise Tolerance

Seeded 10 durable claims and 90 low-quality observations with `include_observations=true`.

| top_k | durable | observations | durable share | signal:noise ratio |
| ---: | ---: | ---: | ---: | ---: |
| 5 | 5 | 0 | 1 | all_signal |
| 10 | 10 | 0 | 1 | all_signal |
| 20 | 10 | 6 | 0.625 | 1.6667 |

## Experiment 3: Temporal Decay

Thresholded activate labels: `fact_1h`, `task_1h`, `fact_1d`, `fact_1w`, `task_1d`, `fact_30d`, `task_1w`, `fact_90d`

| Ratio | Value |
| --- | ---: |
| fact_90d_vs_fact_1h | 0.7163 |
| task_90d_vs_task_1h | 0.3086 |
| fact_90d_vs_task_90d | 2.3244 |
| fact_30d_vs_task_30d | 1.9381 |

## Experiment 5: Promote Quality

Raw observe score: **0.8**
Promoted claim score: **0.6373**
Direct upsert score: **0.5518**

Promoted metadata: {
  "boundary_check_allowed": true,
  "has_promotion_candidate": true,
  "promotion_status": "accepted",
  "accepted_claim_id": "clm_707fa4dd",
  "evidence_count": 1,
  "evidence_source_types": [
    "observation"
  ],
  "has_source_lineage": true
}

## Experiment 6: Simulated Development Efficiency

WITH-MEMORY session 3 referenced both sessions: **true**
WITHOUT-MEMORY session 3 referenced both sessions: **false**
WITH-MEMORY evidence from both sessions: **true**
WITHOUT-MEMORY evidence from both sessions: **false**

## Key Takeaways

- Retrieval precision averaged Precision@3=0.9333 and NDCG@3=0.9838 across the five directed queries.
- The intent profiles and hard filters behaved as true retrieval controls rather than cosmetic boosts in the seeded scenarios.
- Observation noise did not displace the durable corpus in top-10 for the selected query, but it did fill lower ranks as top_k expanded.
- Temporal decay clearly penalized old task claims more aggressively than old facts, with old tasks dropping below the retrieval threshold sooner.
- Promotion added durable lineage and evidence links; raw observations remained searchable but lacked the boundary-checked promotion metadata.
- The three-session Ollama workflow only cited both prior sessions when activate results were injected from the internal memory store.

# Value Validation Revalidation Comparison

Baseline sources:
- `validation/value/results/report.md` generated at `2026-03-24T22:40:44.438Z`
- `validation/value/results/experiment-results.json` from the same run

After-fixes sources:
- `validation/value/results/report-after-fixes.md` generated at `2026-03-25T01:18:38.661Z`
- `validation/value/results/experiment-results-after-fixes.json` from the same run

Note: the harness currently emits Experiments 1, 2, 3, 5, and 6. There is no Experiment 4 artifact in either run.

| Experiment | Before | After | Expected after #67-#71 | Result |
| --- | --- | --- | --- | --- |
| Experiment 1: Search Precision | Avg `P@3=0.9333`, `NDCG@3=0.9838`; `policy_check_norm_over_task` `P@3=0.6667`, `NDCG@3=0.9468` | Avg `P@3=0.9333`, `NDCG@3=0.9838`; `policy_check_norm_over_task` `P@3=0.6667`, `NDCG@3=0.9468` | `policy_check` should improve via non-norm penalty | Partial. Aggregate metrics and `policy_check` ranking metrics did not move, but the returned memory types for `policy_check` collapsed from `norm/knowledge/working_state` to `norm` only, which shows the non-norm penalty is affecting result composition without improving the top-3 hit rate. |
| Experiment 2: Noise Tolerance | Top-20: `10` durable, `10` observations, durable share `0.5` | Top-20: `10` durable, `6` observations, durable share `0.625`, returned rows `16` | Observation cap should limit noise to 30% | Pass with nuance. Observation count dropped from `10` to `6`; that is exactly `30%` of requested `top_k=20`. Because the capped result set returned `16` rows total, observations are `37.5%` of returned rows. |
| Experiment 3: Temporal Decay | `thresholded_activate_labels` still included `task_30d`; `task_90d_vs_task_1h=0.3086` | `thresholded_activate_labels` exclude both `task_30d` and `task_90d`; `task_90d_vs_task_1h=0.3086` | Stale `working_state` should be excluded | Pass for activate behavior. Old `working_state` entries are now filtered out of thresholded activate results. The diagnostic full-ranking ratios are unchanged, so the fix affects retrieval eligibility rather than raw scoring. |
| Experiment 5: Promote Quality | Raw `1.0`, promoted `0.5255`, direct upsert `0.5255` | Raw `0.8`, promoted `0.6373`, direct upsert `0.5518` | Promoted claim should score higher than before due to provenance quality boost | Pass. Promoted score improved by `+0.1118` and now beats direct upsert by `+0.0855`. It still does not beat the raw observation score. |
| Experiment 6: Simulated Development Efficiency | With-memory referenced both sessions: `true`; without-memory: `false` | With-memory referenced both sessions: `true`; without-memory: `false` | No regression expected | No regression. Behavior stayed stable across the rerun. |

## Bottom Line

- Confirmed improvements:
  - Experiment 2 observation noise fell from `50%` to `30%` of requested top-k.
  - Experiment 3 stale `working_state` claims are no longer present in thresholded activate output.
  - Experiment 5 promoted-claim ranking improved from `0.5255` to `0.6373`.
- Not confirmed:
  - Experiment 1 `policy_check` precision did not improve; it remains `0.6667`.
- Stable:
  - Experiment 6 behavior is unchanged.

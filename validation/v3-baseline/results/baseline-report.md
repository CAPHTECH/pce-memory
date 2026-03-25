# V3 Baseline Benchmark

Generated at: 2026-03-25T06:17:21.169Z

This benchmark uses internal handler imports from `apps/pce-memory/src/`, an isolated `:memory:` DuckDB store per dimension, and a deterministic bag-of-words embedding service for repeatable local execution.

## Score Summary

| Dimension | Score | Metric |
| --- | ---: | --- |
| B1 Freshness | 90% | latest top-1 is newest version |
| B2 Usage Learning | 0.062 | Spearman(freq, final rank) |
| B3 Maintenance | 0% | detected hint categories |
| B4 Connectivity | 60% | related claim recall@5 |
| B5 Combined | 87.5% | mean(freshness,relevance) |

## Notes

- B1 latest top-1 rate: 90%. Pairwise latest-vs-stale win rate: 100%.
- B2 final correlation: 0.062.
- B3 detected categories: none.
- B4 related claim recall@5: 60%.
- B5 freshness pair accuracy: 100%. Relevance precision@8: 75%.

## Interpretation

- B1 is the baseline for future freshness-aware retrieval. Higher post-v3 scores should mean newer claims displace stale variants more reliably.
- B2 isolates usage learning without feedback writes. A post-v3 implementation should move the correlation positive only if plain retrieval history becomes a ranking signal.
- B3 checks whether activate currently surfaces maintenance guidance for duplicates, raw observations, or dormant claims. The current baseline is expected to stay at zero unless new hint fields are introduced.
- B4 measures how often logically related claims appear without graph links. Improvements after connectivity work should raise recall without relying on lexical coincidence.
- B5 gives a single regression-friendly number for a realistic multi-session flow.


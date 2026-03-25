# Post-Extractor-Removal Validation Check

Generated: 2026-03-25T14:14:25+09:00

## Step 1: Workspace Validation

Commands run:

```bash
pnpm install
pnpm build
pnpm test
pnpm typecheck
```

Results:

| Command | Status | Pass count | Fail count | Notes |
| --- | --- | ---: | ---: | --- |
| `pnpm install` | PASS | 1 | 0 | Workspace install completed successfully; lockfile already up to date. |
| `pnpm build` | PASS | 5 | 0 | 5 of 5 workspace package/app builds succeeded. |
| `pnpm test` | PASS | 71 | 0 | 71 test files passed; 879 tests passed. |
| `pnpm typecheck` | PASS | 5 | 0 | 5 of 5 workspace package/app typechecks succeeded. |

Overall Step 1 status: `4/4` commands passed.

## Step 2: Value Validation Rerun

Build commands run:

```bash
pnpm --filter '@pce/*' run build
./node_modules/.bin/tsdown validation/value/run-value-tests.ts --format esm --clean --out-dir apps/pce-memory/.validation-dist --tsconfig tsconfig.base.json --external @duckdb/node-api
```

Execution command run:

```bash
node apps/pce-memory/.validation-dist/run-value-tests.js
```

Artifacts regenerated:

- `validation/value/results/experiment-results.json`
- `validation/value/results/report.md`

### Baseline Comparison

Requested baseline:

- Exp1 P@3 = `1.0`
- Exp2 top-20 observations = `6`
- Exp5 promoted claim score = `0.6373`

Prior decay baseline for Exp3 from the checked-in revalidation artifacts:

- Thresholded labels: `fact_1h`, `task_1h`, `fact_1d`, `fact_1w`, `task_1d`, `fact_30d`, `task_1w`, `fact_90d`
- `fact_90d_vs_fact_1h = 0.7163`
- `task_90d_vs_task_1h = 0.3086`
- `fact_90d_vs_task_90d = 2.3244`
- `fact_30d_vs_task_30d = 1.9381`

Current results:

| Experiment | Baseline | Current | Result |
| --- | --- | --- | --- |
| Exp1 Search Precision | Avg `P@3=1.0` | Avg `P@3=1.0`, Avg `NDCG@3=0.9944` | PASS |
| Exp2 Noise Tolerance | `top_k=20` observations `=6` | `top_k=20` observations `=6`, durable `=10`, durable share `=0.625`, returned rows `=16` | PASS |
| Exp3 Temporal Decay | Thresholded labels and ratios listed above | Thresholded labels unchanged; ratios unchanged (`0.7163`, `0.3086`, `2.3244`, `1.9381`) | PASS |
| Exp5 Promote Quality | Promoted claim score `=0.6373` | Raw `=0.8`, promoted `=0.6373`, direct upsert `=0.5518` | PASS |

Notes:

- Exp1 improved relative to the previously checked-in `validation/value/results/report.md` snapshot, which had Avg `P@3=0.9333`; the rerun restored the requested `1.0` baseline.
- Exp2 matches the expected capped-noise behavior after extractor removal; observation count stayed at `6`.
- Exp3 shows no decay regression. Older task claims remain excluded from the thresholded activate output.
- Exp5 matches the requested promoted-quality baseline exactly and still ranks the promoted claim above direct upsert.

## Step 3: Query Expansion Verification

Command run:

```bash
pnpm test -- apps/pce-memory/test/retrieval-query-expansion-experiment.test.ts
```

Result:

| Command | Status | Pass count | Fail count |
| --- | --- | ---: | ---: |
| `retrieval-query-expansion-experiment.test.ts` | PASS | 1 | 0 |

## Conclusion

The post-extractor-removal validation shows no regression in the requested checks:

- Workspace install/build/test/typecheck all passed.
- Value validation met the requested baselines for Exp1, Exp2, Exp3, and Exp5.
- The targeted query-expansion regression test passed.

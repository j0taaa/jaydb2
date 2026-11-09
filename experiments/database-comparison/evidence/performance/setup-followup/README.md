# Setup follow-up

Separate setup-only follow-up; does not overwrite or pass original full-run gates. Three interleaved paired repetitions per originally flagged metric. Alternate A/B then B/A order. Same canonical durable limits, frozen binaries, actual admission and three prepared programs. No workload timings are replaced.

All24 native setup observations passed, including full data readbacks. All copied snapshots, binaries, core source maps and generated/admitted Bend inputs match their original benchmark evidence; originals were not modified. See audit.json.

| Scenario | Metric | Baseline median s | Candidate median s | Median paired change | Paired range |
| --- | --- | ---: | ---: | ---: | ---: |
| 01_personal_tasks | reopen_and_client_prepare_ns | 18.206 | 21.240 | +15.93% | +14.31% to +38.70% |
| 02_household_budget | create_schema_and_client_ns | 19.071 | 23.043 | +20.83% | +18.92% to +30.40% |
| 03_editorial_blog | reopen_and_client_prepare_ns | 18.166 | 22.189 | +17.24% | +16.63% to +24.03% |
| 04_ecommerce | create_schema_and_client_ns | 20.023 | 25.851 | +29.11% | +17.37% to +29.18% |

All twelve paired observations show slower candidate setup. The median paired changes exceed15% for all four originally flagged metrics. This reproduces a setup tradeoff; the original full-run strict latency+setup gate remains failed. Three repetitions do not establish a population confidence bound or exclude other regressions.

Source inspection identifies two extra FastInput/FastBytes modules in authentication and execution compilation closures. Matched compiled C observations show about54KiB extra text with unchanged STAT_LEN for the same configuration/program. This supports compilation footprint as a plausible cause, but no compiler-phase timing attribution was established. A small read-only observer inspected generated public C metadata during later trials; it never altered engine/workload code or private state.

Native work ran serially under the common lock. Order is baseline/candidate for repetitions0 and2 and candidate/baseline for repetition1. Unrelated host activity remains uncontrolled. The diagnostic occurred separately from the original benchmark, and no original sample was replaced.

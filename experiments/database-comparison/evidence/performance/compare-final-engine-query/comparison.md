# Paired benchmark comparison

Configured sampled gate: **gate_failed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `c60a629dd253bbd10bfac71ce154cd2ed6e49989cc5c4c422b644639bc24ed89`
Candidate controller: `c60a629dd253bbd10bfac71ce154cd2ed6e49989cc5c4c422b644639bc24ed89`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency, setup.

Application profiles differ: {"metadata": {}, "profile": "legacy"} -> {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}. This does not isolate an engine optimization.

Measured workload/adapter code differs; this is an application-profile comparison, not an isolated engine optimization.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 57.4299 | 6.3738 | -88.90% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 50.4073 | 19.274 | -61.76% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 423.227 | 82.9755 | -80.39% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 69.6708 | 21.9397 | -68.51% | improvement |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 27539.6 | 64073.5 | +132.66% | regression_exceeds_threshold |
| 01_personal_tasks | jaydb2 | populate_ns | 339.088 | 358.68 | +5.78% | possible_regression |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 31131.7 | 56463.6 | +81.37% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 64.6981 | 9.51785 | -85.29% | improvement |
| 02_household_budget | jaydb2 | point_update | 26.3219 | 19.2232 | -26.97% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 914.662 | 23.2383 | -97.46% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 345.768 | 83.1213 | -75.96% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 22.8532 | 53.3095 | +133.27% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 31948.8 | 69106.6 | +116.30% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 794.157 | 849.258 | +6.94% | possible_regression |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 31215.4 | 42313.3 | +35.55% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | point_read | 31.0749 | 7.66104 | -75.35% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 25.4615 | 63.0061 | +147.46% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | relationship_join | 565.692 | 24.5708 | -95.66% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 298.414 | 19.1684 | -93.58% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 27.0738 | 19.0184 | -29.75% | improvement |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 29660.1 | 38107.1 | +28.48% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | populate_ns | 1644.05 | 1211.65 | -26.30% | improvement |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 26334.9 | 37074.9 | +40.78% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 22.0074 | 8.51448 | -61.31% | improvement |
| 04_ecommerce | jaydb2 | point_update | 23.3101 | 126.29 | +441.78% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | relationship_join | 346.237 | 42.9269 | -87.60% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 191.291 | 85.2103 | -55.46% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 20.6509 | 76.3946 | +269.93% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 34981.5 | 41322 | +18.13% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 1175.21 | 2937.82 | +149.98% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 31447.9 | 37976.9 | +20.76% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | point_read | 24.6596 | 9.5291 | -61.36% | improvement |
| 05_clinic | jaydb2 | point_update | 22.8245 | 22.3876 | -1.91% | within_tolerance |
| 05_clinic | jaydb2 | relationship_join | 577.745 | 19.481 | -96.63% | improvement |
| 05_clinic | jaydb2 | scan_sum | 350.194 | 22.0622 | -93.70% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 26.4332 | 16.7713 | -36.55% | improvement |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 28506.2 | 40271.7 | +41.27% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | populate_ns | 3873.75 | 1817.47 | -53.08% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 22636.9 | 42200.1 | +86.42% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | point_read | 23.4793 | 10.9703 | -53.28% | improvement |
| 06_learning_platform | jaydb2 | point_update | 24.7229 | 23.4538 | -5.13% | improvement |
| 06_learning_platform | jaydb2 | relationship_join | 440.799 | 21.0193 | -95.23% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 214.182 | 24.0985 | -88.75% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 25.3691 | 19.9661 | -21.30% | improvement |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 27671.7 | 41777.9 | +50.98% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | populate_ns | 2084.11 | 2349.5 | +12.73% | possible_regression |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 27312.5 | 44696.3 | +63.65% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | point_read | 24.847 | 12.157 | -51.07% | improvement |
| 07_hotel | jaydb2 | point_update | 26.2943 | 23.0246 | -12.44% | improvement |
| 07_hotel | jaydb2 | relationship_join | 425.853 | 24.3728 | -94.28% | improvement |
| 07_hotel | jaydb2 | scan_sum | 235.906 | 22.906 | -90.29% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 27.0345 | 23.4759 | -13.16% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 25036.5 | 39937 | +59.52% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | populate_ns | 2824.47 | 2550.25 | -9.71% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 29419.4 | 42933.8 | +45.94% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | point_read | 30.03 | 15.3729 | -48.81% | improvement |
| 08_logistics | jaydb2 | point_update | 32.3895 | 62.5199 | +93.03% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | relationship_join | 517.483 | 27.3235 | -94.72% | improvement |
| 08_logistics | jaydb2 | scan_sum | 248.126 | 31.9056 | -87.14% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 29.8723 | 26.7874 | -10.33% | improvement |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 42653.4 | 45958.5 | +7.75% | possible_regression |
| 08_logistics | jaydb2 | populate_ns | 3983.59 | 7266.5 | +82.41% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 37054.2 | 39391.2 | +6.31% | possible_regression |
| 09_manufacturing | jaydb2 | point_read | 33.1081 | 30.7755 | -7.05% | improvement |
| 09_manufacturing | jaydb2 | point_update | 33.5366 | 29.4707 | -12.12% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 647.291 | 26.4348 | -95.92% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 309.567 | 30.7217 | -90.08% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 35.0928 | 27.4298 | -21.84% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 43562.1 | 42263.8 | -2.98% | within_tolerance |
| 09_manufacturing | jaydb2 | populate_ns | 5645.1 | 4641.47 | -17.78% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 38570.8 | 37851.6 | -1.86% | within_tolerance |
| 10_municipal_services | jaydb2 | point_read | 49.7191 | 22.1501 | -55.45% | improvement |
| 10_municipal_services | jaydb2 | point_update | 51.3506 | 33.0127 | -35.71% | improvement |
| 10_municipal_services | jaydb2 | relationship_join | 791.644 | 35.3265 | -95.54% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 410.136 | 33.0522 | -91.94% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 52.444 | 35.0127 | -33.24% | improvement |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 43458.8 | 40784.5 | -6.15% | improvement |
| 10_municipal_services | jaydb2 | populate_ns | 13406.6 | 6489.83 | -51.59% | improvement |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 35572.6 | 37328.8 | +4.94% | within_tolerance |

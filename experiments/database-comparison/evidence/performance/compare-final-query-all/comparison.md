# Paired benchmark comparison

Configured sampled gate: **gate_failed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `62f1f6f4ab9c924c340e2af73012f44f7b9c066749b55b2a5ab74c2c5600f201`
Candidate controller: `c60a629dd253bbd10bfac71ce154cd2ed6e49989cc5c4c422b644639bc24ed89`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency, setup.

Application profiles differ: {"metadata": {}, "profile": "legacy"} -> {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}. This does not isolate an engine optimization.

Measured workload/adapter code differs; this is an application-profile comparison, not an isolated engine optimization.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 85.9618 | 6.3738 | -92.59% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 77.7612 | 19.274 | -75.21% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 734.681 | 82.9755 | -88.71% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 77.0836 | 21.9397 | -71.54% | improvement |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 23094.1 | 64073.5 | +177.44% | regression_exceeds_threshold |
| 01_personal_tasks | jaydb2 | populate_ns | 735.257 | 358.68 | -51.22% | improvement |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 18834.8 | 56463.6 | +199.78% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 111.964 | 9.51785 | -91.50% | improvement |
| 02_household_budget | jaydb2 | point_update | 121.082 | 19.2232 | -84.12% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 1876.73 | 23.2383 | -98.76% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 1023.93 | 83.1213 | -91.88% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 125.659 | 53.3095 | -57.58% | improvement |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 21323.9 | 69106.6 | +224.08% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 2507.67 | 849.258 | -66.13% | improvement |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 25075.1 | 42313.3 | +68.75% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | point_read | 85.7547 | 7.66104 | -91.07% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 83.4675 | 63.0061 | -24.51% | improvement |
| 03_editorial_blog | jaydb2 | relationship_join | 1498.47 | 24.5708 | -98.36% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 775.102 | 19.1684 | -97.53% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 88.051 | 19.0184 | -78.40% | improvement |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 22582.8 | 38107.1 | +68.74% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | populate_ns | 3650.95 | 1211.65 | -66.81% | improvement |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 20226.4 | 37074.9 | +83.30% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 103.383 | 8.51448 | -91.76% | improvement |
| 04_ecommerce | jaydb2 | point_update | 102.27 | 126.29 | +23.49% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | relationship_join | 1758.2 | 42.9269 | -97.56% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 909.739 | 85.2103 | -90.63% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 93.9393 | 76.3946 | -18.68% | improvement |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 21586.2 | 41322 | +91.43% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 5612.04 | 2937.82 | -47.65% | improvement |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 22167.6 | 37976.9 | +71.32% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | point_read | 132.917 | 9.5291 | -92.83% | improvement |
| 05_clinic | jaydb2 | point_update | 116.187 | 22.3876 | -80.73% | improvement |
| 05_clinic | jaydb2 | relationship_join | 1927.21 | 19.481 | -98.99% | improvement |
| 05_clinic | jaydb2 | scan_sum | 1032.52 | 22.0622 | -97.86% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 112.565 | 16.7713 | -85.10% | improvement |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 29031.7 | 40271.7 | +38.72% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | populate_ns | 16209.5 | 1817.47 | -88.79% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 41997.5 | 42200.1 | +0.48% | within_tolerance |
| 06_learning_platform | jaydb2 | point_read | 128.644 | 10.9703 | -91.47% | improvement |
| 06_learning_platform | jaydb2 | point_update | 135.034 | 23.4538 | -82.63% | improvement |
| 06_learning_platform | jaydb2 | relationship_join | 2709.95 | 21.0193 | -99.22% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 1330.89 | 24.0985 | -98.19% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 143.139 | 19.9661 | -86.05% | improvement |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 37602.5 | 41777.9 | +11.10% | possible_regression |
| 06_learning_platform | jaydb2 | populate_ns | 27554.1 | 2349.5 | -91.47% | improvement |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 22776.6 | 44696.3 | +96.24% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | point_read | 102.264 | 12.157 | -88.11% | improvement |
| 07_hotel | jaydb2 | point_update | 103.463 | 23.0246 | -77.75% | improvement |
| 07_hotel | jaydb2 | relationship_join | 1815.11 | 24.3728 | -98.66% | improvement |
| 07_hotel | jaydb2 | scan_sum | 973.405 | 22.906 | -97.65% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 96.1895 | 23.4759 | -75.59% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 26161.8 | 39937 | +52.65% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | populate_ns | 15033.9 | 2550.25 | -83.04% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 23663.3 | 42933.8 | +81.44% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | point_read | 180.614 | 15.3729 | -91.49% | improvement |
| 08_logistics | jaydb2 | point_update | 145.168 | 62.5199 | -56.93% | improvement |
| 08_logistics | jaydb2 | relationship_join | 2487.02 | 27.3235 | -98.90% | improvement |
| 08_logistics | jaydb2 | scan_sum | 1292.07 | 31.9056 | -97.53% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 150.092 | 26.7874 | -82.15% | improvement |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 22934.6 | 45958.5 | +100.39% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | populate_ns | 14446.5 | 7266.5 | -49.70% | improvement |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 25510.6 | 39391.2 | +54.41% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | point_read | 95.8573 | 30.7755 | -67.89% | improvement |
| 09_manufacturing | jaydb2 | point_update | 105.045 | 29.4707 | -71.94% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 1804.05 | 26.4348 | -98.53% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 856.953 | 30.7217 | -96.42% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 92.995 | 27.4298 | -70.50% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 26665.7 | 42263.8 | +58.49% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | populate_ns | 23334.5 | 4641.47 | -80.11% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 28337.3 | 37851.6 | +33.58% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | point_read | 130.176 | 22.1501 | -82.98% | improvement |
| 10_municipal_services | jaydb2 | point_update | 162.283 | 33.0127 | -79.66% | improvement |
| 10_municipal_services | jaydb2 | relationship_join | 2197.71 | 35.3265 | -98.39% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 1322.73 | 33.0522 | -97.50% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 170.242 | 35.0127 | -79.43% | improvement |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 30447 | 40784.5 | +33.95% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | populate_ns | 41262.9 | 6489.83 | -84.27% | improvement |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 25293.6 | 37328.8 | +47.58% | regression_exceeds_threshold |

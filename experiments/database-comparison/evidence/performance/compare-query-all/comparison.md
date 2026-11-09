# Paired benchmark comparison

Configured sampled gate: **gate_failed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `62f1f6f4ab9c924c340e2af73012f44f7b9c066749b55b2a5ab74c2c5600f201`
Candidate controller: `da1ef7906f279d9d54358655afa3965fb618acf07e41c1c866810da3f1b33fe9`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency, setup.

Application profiles differ: {"metadata": {}, "profile": "legacy"} -> {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}. This does not isolate an engine optimization.

Measured workload/adapter code differs; this is an application-profile comparison, not an isolated engine optimization.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 85.9618 | 5.09118 | -94.08% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 77.7612 | 15.1694 | -80.49% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 734.681 | 15.2571 | -97.92% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 77.0836 | 17.1506 | -77.75% | improvement |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 23094.1 | 46717.6 | +102.29% | regression_exceeds_threshold |
| 01_personal_tasks | jaydb2 | populate_ns | 735.257 | 144.942 | -80.29% | improvement |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 18834.8 | 43518.9 | +131.06% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 111.964 | 5.60027 | -95.00% | improvement |
| 02_household_budget | jaydb2 | point_update | 121.082 | 17.1752 | -85.82% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 1876.73 | 15.894 | -99.15% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 1023.93 | 17.8921 | -98.25% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 125.659 | 16.022 | -87.25% | improvement |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 21323.9 | 46899.1 | +119.94% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 2507.67 | 534.081 | -78.70% | improvement |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 25075.1 | 44721.9 | +78.35% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | point_read | 85.7547 | 8.86993 | -89.66% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 83.4675 | 75.1016 | -10.02% | improvement |
| 03_editorial_blog | jaydb2 | relationship_join | 1498.47 | 98.0058 | -93.46% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 775.102 | 64.9481 | -91.62% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 88.051 | 70.5325 | -19.90% | improvement |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 22582.8 | 47058.3 | +108.38% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | populate_ns | 3650.95 | 6918.84 | +89.51% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 20226.4 | 45879.9 | +126.83% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 103.383 | 9.21776 | -91.08% | improvement |
| 04_ecommerce | jaydb2 | point_update | 102.27 | 79.817 | -21.95% | improvement |
| 04_ecommerce | jaydb2 | relationship_join | 1758.2 | 81.5557 | -95.36% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 909.739 | 42.5811 | -95.32% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 93.9393 | 76.5181 | -18.55% | improvement |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 21586.2 | 45432.5 | +110.47% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 5612.04 | 4298.64 | -23.40% | improvement |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 22167.6 | 46216.2 | +108.49% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | point_read | 132.917 | 32.3267 | -75.68% | improvement |
| 05_clinic | jaydb2 | point_update | 116.187 | 63.7028 | -45.17% | improvement |
| 05_clinic | jaydb2 | relationship_join | 1927.21 | 128.322 | -93.34% | improvement |
| 05_clinic | jaydb2 | scan_sum | 1032.52 | 72.4545 | -92.98% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 112.565 | 76.0188 | -32.47% | improvement |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 29031.7 | 45765.3 | +57.64% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | populate_ns | 16209.5 | 3736.92 | -76.95% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 41997.5 | 44177.1 | +5.19% | possible_regression |
| 06_learning_platform | jaydb2 | point_read | 128.644 | 21.9947 | -82.90% | improvement |
| 06_learning_platform | jaydb2 | point_update | 135.034 | 60.9486 | -54.86% | improvement |
| 06_learning_platform | jaydb2 | relationship_join | 2709.95 | 46.4682 | -98.29% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 1330.89 | 67.5397 | -94.93% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 143.139 | 38.6269 | -73.01% | improvement |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 37602.5 | 46582.2 | +23.88% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | populate_ns | 27554.1 | 5653.83 | -79.48% | improvement |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 22776.6 | 44779 | +96.60% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | point_read | 102.264 | 12.8241 | -87.46% | improvement |
| 07_hotel | jaydb2 | point_update | 103.463 | 23.7371 | -77.06% | improvement |
| 07_hotel | jaydb2 | relationship_join | 1815.11 | 24.1741 | -98.67% | improvement |
| 07_hotel | jaydb2 | scan_sum | 973.405 | 24.5748 | -97.48% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 96.1895 | 24.3076 | -74.73% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 26161.8 | 47301.9 | +80.81% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | populate_ns | 15033.9 | 2930.03 | -80.51% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 23663.3 | 44610.8 | +88.52% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | point_read | 180.614 | 15.4666 | -91.44% | improvement |
| 08_logistics | jaydb2 | point_update | 145.168 | 24.5458 | -83.09% | improvement |
| 08_logistics | jaydb2 | relationship_join | 2487.02 | 28.6457 | -98.85% | improvement |
| 08_logistics | jaydb2 | scan_sum | 1292.07 | 28.0315 | -97.83% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 150.092 | 25.9957 | -82.68% | improvement |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 22934.6 | 48799.6 | +112.78% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | populate_ns | 14446.5 | 3382.58 | -76.59% | improvement |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 25510.6 | 44190.3 | +73.22% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | point_read | 95.8573 | 18.1519 | -81.06% | improvement |
| 09_manufacturing | jaydb2 | point_update | 105.045 | 29.5594 | -71.86% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 1804.05 | 33.0696 | -98.17% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 856.953 | 29.306 | -96.58% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 92.995 | 28.2671 | -69.60% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 26665.7 | 48113.6 | +80.43% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | populate_ns | 23334.5 | 5123.52 | -78.04% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 28337.3 | 45643.3 | +61.07% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | point_read | 130.176 | 24.8052 | -80.94% | improvement |
| 10_municipal_services | jaydb2 | point_update | 162.283 | 33.5901 | -79.30% | improvement |
| 10_municipal_services | jaydb2 | relationship_join | 2197.71 | 36.1377 | -98.36% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 1322.73 | 35.7347 | -97.30% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 170.242 | 33.1422 | -80.53% | improvement |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 30447 | 49892.8 | +63.87% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | populate_ns | 41262.9 | 6673.21 | -83.83% | improvement |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 25293.6 | 46292.9 | +83.02% | regression_exceeds_threshold |

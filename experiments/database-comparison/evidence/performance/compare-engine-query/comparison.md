# Paired benchmark comparison

Configured sampled gate: **gate_failed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `da1ef7906f279d9d54358655afa3965fb618acf07e41c1c866810da3f1b33fe9`
Candidate controller: `da1ef7906f279d9d54358655afa3965fb618acf07e41c1c866810da3f1b33fe9`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency, setup.

Application profiles differ: {"metadata": {}, "profile": "legacy"} -> {"metadata": {"comparison": "Application-profile comparison, not an isolated engine change. Compare with --allow-workload-change.", "durability": "Original durable settings and size limits retained. Only genuinely certified reads may reuse the already durable root.", "full_data_validation": "Existing six-cell ReadRow program, additionally read-only-certified; all rows still verified outside timed samples.", "join": "One generic actual-enumeration transaction; child-parent inner join, no row bound or cached answers.", "logical_workloads": "Original scenario inputs, exact-type oracle, sample order, checks and timing boundary are reused unchanged.", "point_reads_and_keys": "One separately read-only-certified Reader program; normal fresh authentication and artifact checks.", "query_registration": "SUM and JOIN use ordinary universal opcode 0 with actual-state termination; no read-only lane is claimed for them.", "setup": "All six programs are actually admitted/prepared and their setup costs are included, including after service reopen.", "sum": "One generic actual-enumeration transaction; exact signed64 checked accumulation, empty zero, overflow refusal."}, "profile": "single-call-queries-v1"}. This does not isolate an engine optimization.

Measured workload/adapter code differs; this is an application-profile comparison, not an isolated engine optimization.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 16.7701 | 5.09118 | -69.64% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 19.9424 | 15.1694 | -23.93% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 159.339 | 15.2571 | -90.42% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 17.9364 | 17.1506 | -4.38% | within_tolerance |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 24449.9 | 46717.6 | +91.07% | regression_exceeds_threshold |
| 01_personal_tasks | jaydb2 | populate_ns | 130.706 | 144.942 | +10.89% | possible_regression |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 23637.6 | 43518.9 | +84.11% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 19.7788 | 5.60027 | -71.69% | improvement |
| 02_household_budget | jaydb2 | point_update | 18.7657 | 17.1752 | -8.48% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 315.221 | 15.894 | -94.96% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 161.542 | 17.8921 | -88.92% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 19.003 | 16.022 | -15.69% | improvement |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 25748.8 | 46899.1 | +82.14% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 458.665 | 534.081 | +16.44% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 24737.1 | 44721.9 | +80.79% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | point_read | 18.6827 | 8.86993 | -52.52% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 19.1901 | 75.1016 | +291.36% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | relationship_join | 354.603 | 98.0058 | -72.36% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 257.178 | 64.9481 | -74.75% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 21.5256 | 70.5325 | +227.67% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 25467.1 | 47058.3 | +84.78% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | populate_ns | 923.454 | 6918.84 | +649.23% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 23590.4 | 45879.9 | +94.49% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 19.5739 | 9.21776 | -52.91% | improvement |
| 04_ecommerce | jaydb2 | point_update | 19.4261 | 79.817 | +310.87% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | relationship_join | 406.095 | 81.5557 | -79.92% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 201.378 | 42.5811 | -78.86% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 20.207 | 76.5181 | +278.67% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 26522.4 | 45432.5 | +71.30% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 1589.67 | 4298.64 | +170.41% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 24794.8 | 46216.2 | +86.39% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | point_read | 34.1206 | 32.3267 | -5.26% | improvement |
| 05_clinic | jaydb2 | point_update | 66.9789 | 63.7028 | -4.89% | within_tolerance |
| 05_clinic | jaydb2 | relationship_join | 880.505 | 128.322 | -85.43% | improvement |
| 05_clinic | jaydb2 | scan_sum | 399.412 | 72.4545 | -81.86% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 55.8969 | 76.0188 | +36.00% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 25432.1 | 45765.3 | +79.95% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | populate_ns | 5515.8 | 3736.92 | -32.25% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 25238.5 | 44177.1 | +75.04% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | point_read | 23.8418 | 21.9947 | -7.75% | improvement |
| 06_learning_platform | jaydb2 | point_update | 22.8872 | 60.9486 | +166.30% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | relationship_join | 500.636 | 46.4682 | -90.72% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 255.6 | 67.5397 | -73.58% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 22.5602 | 38.6269 | +71.22% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 25678.2 | 46582.2 | +81.41% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | populate_ns | 2391.24 | 5653.83 | +136.44% | regression_exceeds_threshold |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 23291.5 | 44779 | +92.25% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | point_read | 24.7185 | 12.8241 | -48.12% | improvement |
| 07_hotel | jaydb2 | point_update | 28.882 | 23.7371 | -17.81% | improvement |
| 07_hotel | jaydb2 | relationship_join | 488.761 | 24.1741 | -95.05% | improvement |
| 07_hotel | jaydb2 | scan_sum | 225.209 | 24.5748 | -89.09% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 28.395 | 24.3076 | -14.39% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 26777.1 | 47301.9 | +76.65% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | populate_ns | 3378.5 | 2930.03 | -13.27% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 24025.3 | 44610.8 | +85.68% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | point_read | 29.7767 | 15.4666 | -48.06% | improvement |
| 08_logistics | jaydb2 | point_update | 33.6791 | 24.5458 | -27.12% | improvement |
| 08_logistics | jaydb2 | relationship_join | 516.827 | 28.6457 | -94.46% | improvement |
| 08_logistics | jaydb2 | scan_sum | 266.513 | 28.0315 | -89.48% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 26.6086 | 25.9957 | -2.30% | within_tolerance |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 25901.3 | 48799.6 | +88.41% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | populate_ns | 3494.35 | 3382.58 | -3.20% | within_tolerance |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 24045.8 | 44190.3 | +83.78% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | point_read | 50.7101 | 18.1519 | -64.20% | improvement |
| 09_manufacturing | jaydb2 | point_update | 70.0909 | 29.5594 | -57.83% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 1049.37 | 33.0696 | -96.85% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 468.01 | 29.306 | -93.74% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 68.902 | 28.2671 | -58.97% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 27007.9 | 48113.6 | +78.15% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | populate_ns | 9996.88 | 5123.52 | -48.75% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 26617.5 | 45643.3 | +71.48% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | point_read | 34.4303 | 24.8052 | -27.96% | improvement |
| 10_municipal_services | jaydb2 | point_update | 33.6968 | 33.5901 | -0.32% | within_tolerance |
| 10_municipal_services | jaydb2 | relationship_join | 672.547 | 36.1377 | -94.63% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 325.619 | 35.7347 | -89.03% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 33.9161 | 33.1422 | -2.28% | within_tolerance |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 28624.2 | 49892.8 | +74.30% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | populate_ns | 5955.42 | 6673.21 | +12.05% | possible_regression |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 24992.7 | 46292.9 | +85.23% | regression_exceeds_threshold |

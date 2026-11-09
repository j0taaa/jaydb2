# Paired benchmark comparison

Configured sampled gate: **gate_passed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `62f1f6f4ab9c924c340e2af73012f44f7b9c066749b55b2a5ab74c2c5600f201`
Candidate controller: `da1ef7906f279d9d54358655afa3965fb618acf07e41c1c866810da3f1b33fe9`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {}, "profile": "legacy"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 85.9618 | 16.7701 | -80.49% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 77.7612 | 19.9424 | -74.35% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 734.681 | 159.339 | -78.31% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 77.0836 | 17.9364 | -76.73% | improvement |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 23094.1 | 24449.9 | +5.87% | possible_regression |
| 01_personal_tasks | jaydb2 | populate_ns | 735.257 | 130.706 | -82.22% | improvement |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 18834.8 | 23637.6 | +25.50% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 111.964 | 19.7788 | -82.33% | improvement |
| 02_household_budget | jaydb2 | point_update | 121.082 | 18.7657 | -84.50% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 1876.73 | 315.221 | -83.20% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 1023.93 | 161.542 | -84.22% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 125.659 | 19.003 | -84.88% | improvement |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 21323.9 | 25748.8 | +20.75% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 2507.67 | 458.665 | -81.71% | improvement |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 25075.1 | 24737.1 | -1.35% | within_tolerance |
| 03_editorial_blog | jaydb2 | point_read | 85.7547 | 18.6827 | -78.21% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 83.4675 | 19.1901 | -77.01% | improvement |
| 03_editorial_blog | jaydb2 | relationship_join | 1498.47 | 354.603 | -76.34% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 775.102 | 257.178 | -66.82% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 88.051 | 21.5256 | -75.55% | improvement |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 22582.8 | 25467.1 | +12.77% | possible_regression |
| 03_editorial_blog | jaydb2 | populate_ns | 3650.95 | 923.454 | -74.71% | improvement |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 20226.4 | 23590.4 | +16.63% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 103.383 | 19.5739 | -81.07% | improvement |
| 04_ecommerce | jaydb2 | point_update | 102.27 | 19.4261 | -81.01% | improvement |
| 04_ecommerce | jaydb2 | relationship_join | 1758.2 | 406.095 | -76.90% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 909.739 | 201.378 | -77.86% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 93.9393 | 20.207 | -78.49% | improvement |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 21586.2 | 26522.4 | +22.87% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 5612.04 | 1589.67 | -71.67% | improvement |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 22167.6 | 24794.8 | +11.85% | possible_regression |
| 05_clinic | jaydb2 | point_read | 132.917 | 34.1206 | -74.33% | improvement |
| 05_clinic | jaydb2 | point_update | 116.187 | 66.9789 | -42.35% | improvement |
| 05_clinic | jaydb2 | relationship_join | 1927.21 | 880.505 | -54.31% | improvement |
| 05_clinic | jaydb2 | scan_sum | 1032.52 | 399.412 | -61.32% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 112.565 | 55.8969 | -50.34% | improvement |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 29031.7 | 25432.1 | -12.40% | improvement |
| 05_clinic | jaydb2 | populate_ns | 16209.5 | 5515.8 | -65.97% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 41997.5 | 25238.5 | -39.90% | improvement |
| 06_learning_platform | jaydb2 | point_read | 128.644 | 23.8418 | -81.47% | improvement |
| 06_learning_platform | jaydb2 | point_update | 135.034 | 22.8872 | -83.05% | improvement |
| 06_learning_platform | jaydb2 | relationship_join | 2709.95 | 500.636 | -81.53% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 1330.89 | 255.6 | -80.79% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 143.139 | 22.5602 | -84.24% | improvement |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 37602.5 | 25678.2 | -31.71% | improvement |
| 06_learning_platform | jaydb2 | populate_ns | 27554.1 | 2391.24 | -91.32% | improvement |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 22776.6 | 23291.5 | +2.26% | within_tolerance |
| 07_hotel | jaydb2 | point_read | 102.264 | 24.7185 | -75.83% | improvement |
| 07_hotel | jaydb2 | point_update | 103.463 | 28.882 | -72.08% | improvement |
| 07_hotel | jaydb2 | relationship_join | 1815.11 | 488.761 | -73.07% | improvement |
| 07_hotel | jaydb2 | scan_sum | 973.405 | 225.209 | -76.86% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 96.1895 | 28.395 | -70.48% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 26161.8 | 26777.1 | +2.35% | within_tolerance |
| 07_hotel | jaydb2 | populate_ns | 15033.9 | 3378.5 | -77.53% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 23663.3 | 24025.3 | +1.53% | within_tolerance |
| 08_logistics | jaydb2 | point_read | 180.614 | 29.7767 | -83.51% | improvement |
| 08_logistics | jaydb2 | point_update | 145.168 | 33.6791 | -76.80% | improvement |
| 08_logistics | jaydb2 | relationship_join | 2487.02 | 516.827 | -79.22% | improvement |
| 08_logistics | jaydb2 | scan_sum | 1292.07 | 266.513 | -79.37% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 150.092 | 26.6086 | -82.27% | improvement |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 22934.6 | 25901.3 | +12.94% | possible_regression |
| 08_logistics | jaydb2 | populate_ns | 14446.5 | 3494.35 | -75.81% | improvement |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 25510.6 | 24045.8 | -5.74% | improvement |
| 09_manufacturing | jaydb2 | point_read | 95.8573 | 50.7101 | -47.10% | improvement |
| 09_manufacturing | jaydb2 | point_update | 105.045 | 70.0909 | -33.27% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 1804.05 | 1049.37 | -41.83% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 856.953 | 468.01 | -45.39% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 92.995 | 68.902 | -25.91% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 26665.7 | 27007.9 | +1.28% | within_tolerance |
| 09_manufacturing | jaydb2 | populate_ns | 23334.5 | 9996.88 | -57.16% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 28337.3 | 26617.5 | -6.07% | improvement |
| 10_municipal_services | jaydb2 | point_read | 130.176 | 34.4303 | -73.55% | improvement |
| 10_municipal_services | jaydb2 | point_update | 162.283 | 33.6968 | -79.24% | improvement |
| 10_municipal_services | jaydb2 | relationship_join | 2197.71 | 672.547 | -69.40% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 1322.73 | 325.619 | -75.38% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 170.242 | 33.9161 | -80.08% | improvement |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 30447 | 28624.2 | -5.99% | improvement |
| 10_municipal_services | jaydb2 | populate_ns | 41262.9 | 5955.42 | -85.57% | improvement |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 25293.6 | 24992.7 | -1.19% | within_tolerance |

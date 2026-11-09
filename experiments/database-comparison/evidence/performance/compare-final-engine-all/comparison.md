# Paired benchmark comparison

Configured sampled gate: **gate_failed**.

All paired observations retained. Medians are recomputed from raw samples. No composite score or workload weighting. Setup has one observation per scenario. Tolerances classify observed changes, not statistical significance; passing cannot establish absence of regressions.

Baseline controller: `62f1f6f4ab9c924c340e2af73012f44f7b9c066749b55b2a5ab74c2c5600f201`
Candidate controller: `c60a629dd253bbd10bfac71ce154cd2ed6e49989cc5c4c422b644639bc24ed89`

Application profiles: `{"baseline": {"metadata": {}, "profile": "legacy"}, "candidate": {"metadata": {}, "profile": "legacy"}}`

Noise tolerance: 5%; regression threshold: 15%; gated metrics: latency, setup.

Every paired measurement (negative change is faster):

| Scenario | Engine | Metric | Baseline ms | Candidate ms | Change | Classification |
| --- | --- | --- | ---: | ---: | ---: | --- |
| 01_personal_tasks | jaydb2 | point_read | 85.9618 | 57.4299 | -33.19% | improvement |
| 01_personal_tasks | jaydb2 | point_update | 77.7612 | 50.4073 | -35.18% | improvement |
| 01_personal_tasks | jaydb2 | scan_sum | 734.681 | 423.227 | -42.39% | improvement |
| 01_personal_tasks | jaydb2 | two_row_transaction | 77.0836 | 69.6708 | -9.62% | improvement |
| 01_personal_tasks | jaydb2 | create_schema_and_client_ns | 23094.1 | 27539.6 | +19.25% | regression_exceeds_threshold |
| 01_personal_tasks | jaydb2 | populate_ns | 735.257 | 339.088 | -53.88% | improvement |
| 01_personal_tasks | jaydb2 | reopen_and_client_prepare_ns | 18834.8 | 31131.7 | +65.29% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | point_read | 111.964 | 64.6981 | -42.22% | improvement |
| 02_household_budget | jaydb2 | point_update | 121.082 | 26.3219 | -78.26% | improvement |
| 02_household_budget | jaydb2 | relationship_join | 1876.73 | 914.662 | -51.26% | improvement |
| 02_household_budget | jaydb2 | scan_sum | 1023.93 | 345.768 | -66.23% | improvement |
| 02_household_budget | jaydb2 | two_row_transaction | 125.659 | 22.8532 | -81.81% | improvement |
| 02_household_budget | jaydb2 | create_schema_and_client_ns | 21323.9 | 31948.8 | +49.83% | regression_exceeds_threshold |
| 02_household_budget | jaydb2 | populate_ns | 2507.67 | 794.157 | -68.33% | improvement |
| 02_household_budget | jaydb2 | reopen_and_client_prepare_ns | 25075.1 | 31215.4 | +24.49% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | point_read | 85.7547 | 31.0749 | -63.76% | improvement |
| 03_editorial_blog | jaydb2 | point_update | 83.4675 | 25.4615 | -69.50% | improvement |
| 03_editorial_blog | jaydb2 | relationship_join | 1498.47 | 565.692 | -62.25% | improvement |
| 03_editorial_blog | jaydb2 | scan_sum | 775.102 | 298.414 | -61.50% | improvement |
| 03_editorial_blog | jaydb2 | two_row_transaction | 88.051 | 27.0738 | -69.25% | improvement |
| 03_editorial_blog | jaydb2 | create_schema_and_client_ns | 22582.8 | 29660.1 | +31.34% | regression_exceeds_threshold |
| 03_editorial_blog | jaydb2 | populate_ns | 3650.95 | 1644.05 | -54.97% | improvement |
| 03_editorial_blog | jaydb2 | reopen_and_client_prepare_ns | 20226.4 | 26334.9 | +30.20% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | point_read | 103.383 | 22.0074 | -78.71% | improvement |
| 04_ecommerce | jaydb2 | point_update | 102.27 | 23.3101 | -77.21% | improvement |
| 04_ecommerce | jaydb2 | relationship_join | 1758.2 | 346.237 | -80.31% | improvement |
| 04_ecommerce | jaydb2 | scan_sum | 909.739 | 191.291 | -78.97% | improvement |
| 04_ecommerce | jaydb2 | two_row_transaction | 93.9393 | 20.6509 | -78.02% | improvement |
| 04_ecommerce | jaydb2 | create_schema_and_client_ns | 21586.2 | 34981.5 | +62.06% | regression_exceeds_threshold |
| 04_ecommerce | jaydb2 | populate_ns | 5612.04 | 1175.21 | -79.06% | improvement |
| 04_ecommerce | jaydb2 | reopen_and_client_prepare_ns | 22167.6 | 31447.9 | +41.86% | regression_exceeds_threshold |
| 05_clinic | jaydb2 | point_read | 132.917 | 24.6596 | -81.45% | improvement |
| 05_clinic | jaydb2 | point_update | 116.187 | 22.8245 | -80.36% | improvement |
| 05_clinic | jaydb2 | relationship_join | 1927.21 | 577.745 | -70.02% | improvement |
| 05_clinic | jaydb2 | scan_sum | 1032.52 | 350.194 | -66.08% | improvement |
| 05_clinic | jaydb2 | two_row_transaction | 112.565 | 26.4332 | -76.52% | improvement |
| 05_clinic | jaydb2 | create_schema_and_client_ns | 29031.7 | 28506.2 | -1.81% | within_tolerance |
| 05_clinic | jaydb2 | populate_ns | 16209.5 | 3873.75 | -76.10% | improvement |
| 05_clinic | jaydb2 | reopen_and_client_prepare_ns | 41997.5 | 22636.9 | -46.10% | improvement |
| 06_learning_platform | jaydb2 | point_read | 128.644 | 23.4793 | -81.75% | improvement |
| 06_learning_platform | jaydb2 | point_update | 135.034 | 24.7229 | -81.69% | improvement |
| 06_learning_platform | jaydb2 | relationship_join | 2709.95 | 440.799 | -83.73% | improvement |
| 06_learning_platform | jaydb2 | scan_sum | 1330.89 | 214.182 | -83.91% | improvement |
| 06_learning_platform | jaydb2 | two_row_transaction | 143.139 | 25.3691 | -82.28% | improvement |
| 06_learning_platform | jaydb2 | create_schema_and_client_ns | 37602.5 | 27671.7 | -26.41% | improvement |
| 06_learning_platform | jaydb2 | populate_ns | 27554.1 | 2084.11 | -92.44% | improvement |
| 06_learning_platform | jaydb2 | reopen_and_client_prepare_ns | 22776.6 | 27312.5 | +19.92% | regression_exceeds_threshold |
| 07_hotel | jaydb2 | point_read | 102.264 | 24.847 | -75.70% | improvement |
| 07_hotel | jaydb2 | point_update | 103.463 | 26.2943 | -74.59% | improvement |
| 07_hotel | jaydb2 | relationship_join | 1815.11 | 425.853 | -76.54% | improvement |
| 07_hotel | jaydb2 | scan_sum | 973.405 | 235.906 | -75.76% | improvement |
| 07_hotel | jaydb2 | two_row_transaction | 96.1895 | 27.0345 | -71.89% | improvement |
| 07_hotel | jaydb2 | create_schema_and_client_ns | 26161.8 | 25036.5 | -4.30% | within_tolerance |
| 07_hotel | jaydb2 | populate_ns | 15033.9 | 2824.47 | -81.21% | improvement |
| 07_hotel | jaydb2 | reopen_and_client_prepare_ns | 23663.3 | 29419.4 | +24.32% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | point_read | 180.614 | 30.03 | -83.37% | improvement |
| 08_logistics | jaydb2 | point_update | 145.168 | 32.3895 | -77.69% | improvement |
| 08_logistics | jaydb2 | relationship_join | 2487.02 | 517.483 | -79.19% | improvement |
| 08_logistics | jaydb2 | scan_sum | 1292.07 | 248.126 | -80.80% | improvement |
| 08_logistics | jaydb2 | two_row_transaction | 150.092 | 29.8723 | -80.10% | improvement |
| 08_logistics | jaydb2 | create_schema_and_client_ns | 22934.6 | 42653.4 | +85.98% | regression_exceeds_threshold |
| 08_logistics | jaydb2 | populate_ns | 14446.5 | 3983.59 | -72.43% | improvement |
| 08_logistics | jaydb2 | reopen_and_client_prepare_ns | 25510.6 | 37054.2 | +45.25% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | point_read | 95.8573 | 33.1081 | -65.46% | improvement |
| 09_manufacturing | jaydb2 | point_update | 105.045 | 33.5366 | -68.07% | improvement |
| 09_manufacturing | jaydb2 | relationship_join | 1804.05 | 647.291 | -64.12% | improvement |
| 09_manufacturing | jaydb2 | scan_sum | 856.953 | 309.567 | -63.88% | improvement |
| 09_manufacturing | jaydb2 | two_row_transaction | 92.995 | 35.0928 | -62.26% | improvement |
| 09_manufacturing | jaydb2 | create_schema_and_client_ns | 26665.7 | 43562.1 | +63.36% | regression_exceeds_threshold |
| 09_manufacturing | jaydb2 | populate_ns | 23334.5 | 5645.1 | -75.81% | improvement |
| 09_manufacturing | jaydb2 | reopen_and_client_prepare_ns | 28337.3 | 38570.8 | +36.11% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | point_read | 130.176 | 49.7191 | -61.81% | improvement |
| 10_municipal_services | jaydb2 | point_update | 162.283 | 51.3506 | -68.36% | improvement |
| 10_municipal_services | jaydb2 | relationship_join | 2197.71 | 791.644 | -63.98% | improvement |
| 10_municipal_services | jaydb2 | scan_sum | 1322.73 | 410.136 | -68.99% | improvement |
| 10_municipal_services | jaydb2 | two_row_transaction | 170.242 | 52.444 | -69.19% | improvement |
| 10_municipal_services | jaydb2 | create_schema_and_client_ns | 30447 | 43458.8 | +42.74% | regression_exceeds_threshold |
| 10_municipal_services | jaydb2 | populate_ns | 41262.9 | 13406.6 | -67.51% | improvement |
| 10_municipal_services | jaydb2 | reopen_and_client_prepare_ns | 25293.6 | 35572.6 | +40.64% | regression_exceeds_threshold |

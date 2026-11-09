| Workload | Jay baseline ms | Jay engine ms | Paired speedup | Jay single-call ms | Paired speedup | PostgreSQL ms | SQLite ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Point read | 107.674 | 24.280 | 4.86× | 14.145 | 8.82× | 0.1118 | 0.0085 |
| Point update | 110.616 | 25.885 | 4.33× | 31.575 | 3.96× | 2.6935 | 6.8775 |
| Two-row transaction | 104.377 | 24.584 | 4.47× | 30.705 | 3.83× | 3.4363 | 6.4815 |
| SUM | 998.669 | 256.389 | 4.42× | 32.520 | 33.13× | 0.1228 | 0.0108 |
| JOIN | 1876.728 | 500.636 | 4.23× | 36.138 | 58.32× | 0.1421 | 0.0289 |

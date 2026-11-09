| Workload | Jay baseline ms | Jay engine ms | Paired speedup | Jay single-call ms | Paired speedup | PostgreSQL ms | SQLite ms |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Point read | 107.674 | 30.552 | 3.51× | 10.250 | 11.74× | 0.0893 | 0.0100 |
| Point update | 110.616 | 26.308 | 4.16× | 26.462 | 4.26× | 3.3145 | 6.2066 |
| Two-row transaction | 104.377 | 27.054 | 3.91× | 25.132 | 4.36× | 3.7196 | 6.5926 |
| SUM | 998.669 | 303.991 | 3.09× | 31.314 | 40.23× | 0.1055 | 0.0136 |
| JOIN | 1876.728 | 565.692 | 3.34× | 24.571 | 74.47× | 0.1396 | 0.0394 |

# Private scalar setup mitigation diagnostic

Separate SHORT mitigation diagnostic: baseline versus PRIVATE scalar prototype, fresh create/schema/client preparation only; no original full-run gate or workload sample is replaced. Three interleaved pairs for each of two originally flagged create metrics.

All12 observations passed actual three-program admission/preparation and complete empty-state readback. Source/binary stability, canonical input equality and prototype source snapshot checks passed; see audit.json. The two touched prototype source files match the bundle whose proofs/build/native checks passed. The production benchmark was not rerun or modified.

| Scenario | Baseline median s | Scalar median s | Median paired change | Paired range |
| --- | ---: | ---: | ---: | ---: |
| 02_household_budget | 20.833 | 19.416 | +5.56% | -9.19% to +11.19% |
| 04_ecommerce | 19.430 | 19.796 | +2.84% | -20.14% to +3.23% |

No pair exceeded15% slowdown in this short diagnostic, versus consistently positive15–29% median paired costs in the original wide-word candidate follow-up. The scalar mechanism therefore mitigates the observed setup problem in these two CREATE cases. It does not demonstrate zero overhead, validate reopen costs, or certify full benchmark regression freedom. Budget median paired cost is still+5.56%, with substantial variation in both directions.

Matched emitted C growth falls from approximately54KiB in the original wide-word candidate to about7.7KiB in the scalar prototype. Dependencies remain two higher and STAT_LEN unchanged. This supports reduced compiler footprint; phase-specific cost attribution was not established.

Fresh durable databases, canonical8MiB/256KiB/256KiB limits and original three program/proof pairs were used. Variant order was baseline/scalar, scalar/baseline, baseline/scalar. Native work ran serially under the common lock; unrelated host load remained uncontrolled. Artifacts were observed only after the timed constructor returned.

One initial metadata construction attempt used the new-candidate source inventory for the older baseline and stopped before any measurement. initial-source-inventory-error.log preserves that failure. The corrected diagnostic uses each variant’s proper inventory and all12 recorded samples ran the same final script.

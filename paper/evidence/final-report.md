# Final controlled JayDB2 thesis evidence

Branch: `t3/integrate-improvements`. Engine source SHA-256: `5b2021cf8f33b0f21e1f87c3f2a3cc4fbaf940cc01c8482b268f2c721c4a95e8`; executable SHA-256: `8848b8348f73a4e0f0731f12500164ca5b31e85cccbcd1b1bdb83a55e716c551`. Raw metadata retain each invocation commit; all refreshed E1–E5 datasets must have identical engine fingerprints.

E1–E3: three fresh sessions per condition. E5: one session, one service per storage mode reused across all sizes. Governor/EPP performance; turbo disabled; nominal 3.6 GHz. No CPU pinning. Inclusive quartiles; no outlier removal.

E3 uses 10 and 1,104 total rows in all engines; owner rows are divided equally between Alice and Bob. SQLite is unconstrained. E4 commands were rerun under the same fixed-clock policy; each wall time is one observation.

All latency rows below use milliseconds. Session spread is min–max of session medians; E5 has only one session. Throughput rows use calls/s.

| Metric | Unit | Pooled median [Q1, Q3] | Session median min–max | n |
|---|---|---|---|---|
| E1 Read | ms | 4,915.382 [4,903.753, 4,938.404] | 4,909.481–4,920.929 | 30 |
| E1 Indexed | ms | 8,846.436 [8,832.265, 8,866.541] | 8,838.316–8,866.044 | 30 |
| E1 Voucher | ms | 9,129.700 [9,107.457, 9,151.513] | 9,113.621–9,139.442 | 30 |
| E2 Read / volatile | ms | 3.913 [3.872, 3.953] | 3.911–3.914 | 900 |
| E2 Read / volatile active throughput | calls/s | 255.507 [254.775, 256.114] | 255.298–255.936 | 30 |
| E2 Read / volatile closed-loop throughput | calls/s | 250.624 [250.539, 250.805] | 250.454–250.986 | 3 |
| E2 Indexed / volatile | ms | 5.950 [5.893, 6.003] | 5.932–5.957 | 900 |
| E2 Indexed / volatile active throughput | calls/s | 167.871 [167.510, 168.525] | 167.630–168.121 | 30 |
| E2 Indexed / volatile closed-loop throughput | calls/s | 165.478 [165.436, 165.690] | 165.394–165.902 | 3 |
| E2 Voucher / volatile | ms | 6.130 [6.079, 6.187] | 6.116–6.137 | 900 |
| E2 Voucher / volatile active throughput | calls/s | 162.855 [162.584, 163.419] | 162.691–163.294 | 30 |
| E2 Voucher / volatile closed-loop throughput | calls/s | 80.258 [80.231, 80.409] | 80.205–80.559 | 3 |
| E2 Read / durable | ms | 3.897 [3.856, 3.947] | 3.885–3.907 | 900 |
| E2 Read / durable active throughput | calls/s | 256.077 [255.430, 256.774] | 255.757–256.734 | 30 |
| E2 Read / durable closed-loop throughput | calls/s | 251.421 [251.057, 251.786] | 250.693–252.151 | 3 |
| E2 Indexed / durable | ms | 16.971 [16.186, 18.333] | 16.777–17.526 | 900 |
| E2 Indexed / durable active throughput | calls/s | 58.690 [57.060, 59.223] | 57.202–59.319 | 30 |
| E2 Indexed / durable closed-loop throughput | calls/s | 57.396 [48.964, 58.162] | 40.533–58.928 | 3 |
| E2 Voucher / durable | ms | 18.702 [17.902, 19.593] | 18.408–19.335 | 900 |
| E2 Voucher / durable active throughput | calls/s | 53.349 [51.123, 55.313] | 51.337–54.300 | 30 |
| E2 Voucher / durable closed-loop throughput | calls/s | 28.831 [28.791, 28.896] | 28.751–28.960 | 3 |
| E3 10 Point PostgreSQL Read | ms | 0.042 [0.041, 0.042] | 0.041–0.042 | 900 |
| E3 10 Point PostgreSQL Update | ms | 3.316 [2.236, 3.547] | 2.303–3.438 | 900 |
| E3 10 Point SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 10 Point SQLite Update | ms | 6.732 [4.452, 7.099] | 5.548–6.797 | 900 |
| E3 10 Point JayDB2 Read | ms | 3.839 [3.799, 3.887] | 3.835–3.847 | 900 |
| E3 10 Point JayDB2 Update | ms | 15.707 [12.771, 17.303] | 14.971–17.248 | 900 |
| E3 10 Owner PostgreSQL Read | ms | 0.042 [0.041, 0.042] | 0.041–0.042 | 900 |
| E3 10 Owner PostgreSQL Update | ms | 3.269 [2.251, 3.494] | 3.224–3.424 | 900 |
| E3 10 Owner SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 10 Owner SQLite Update | ms | 5.814 [4.455, 7.005] | 5.744–6.753 | 900 |
| E3 10 Owner JayDB2 Read | ms | 5.054 [5.008, 5.100] | 5.046–5.063 | 900 |
| E3 10 Owner JayDB2 Update | ms | 16.438 [14.467, 18.168] | 16.072–18.607 | 900 |
| E3 1,104 Point PostgreSQL Read | ms | 0.042 [0.041, 0.043] | 0.042–0.042 | 900 |
| E3 1,104 Point PostgreSQL Update | ms | 2.745 [2.179, 3.454] | 2.604–3.269 | 900 |
| E3 1,104 Point SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 1,104 Point SQLite Update | ms | 2.955 [2.140, 3.437] | 2.940–3.195 | 900 |
| E3 1,104 Point JayDB2 Read | ms | 36.779 [36.617, 36.943] | 36.771–36.795 | 900 |
| E3 1,104 Point JayDB2 Update | ms | 48.943 [47.804, 50.072] | 48.840–49.045 | 900 |
| E3 1,104 Owner PostgreSQL Read | ms | 0.042 [0.042, 0.043] | 0.042–0.042 | 900 |
| E3 1,104 Owner PostgreSQL Update | ms | 3.259 [2.240, 3.448] | 3.254–3.323 | 900 |
| E3 1,104 Owner SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 1,104 Owner SQLite Update | ms | 3.163 [2.076, 3.314] | 2.524–3.249 | 900 |
| E3 1,104 Owner JayDB2 Read | ms | 37.857 [37.707, 38.058] | 37.797–37.974 | 900 |
| E3 1,104 Owner JayDB2 Update | ms | 50.131 [48.895, 52.016] | 49.423–81.830 | 900 |
| E5 10 / volatile Read | ms | 3.854 [3.809, 3.926] | 3.854–3.854 | 50 |
| E5 10 / volatile Update | ms | 3.843 [3.812, 3.897] | 3.843–3.843 | 50 |
| E5 10 / volatile first-key Read | ms | 3.851 [3.813, 3.914] | 3.851–3.851 | 50 |
| E5 30 / volatile Read | ms | 4.471 [4.421, 4.506] | 4.471–4.471 | 50 |
| E5 30 / volatile Update | ms | 4.485 [4.447, 4.535] | 4.485–4.485 | 50 |
| E5 100 / volatile Read | ms | 6.554 [6.495, 6.608] | 6.554–6.554 | 50 |
| E5 100 / volatile Update | ms | 6.556 [6.518, 6.598] | 6.556–6.556 | 50 |
| E5 300 / volatile Read | ms | 12.506 [12.425, 12.583] | 12.506–12.506 | 50 |
| E5 300 / volatile Update | ms | 12.749 [12.639, 12.815] | 12.749–12.749 | 50 |
| E5 600 / volatile Read | ms | 21.548 [21.459, 21.677] | 21.548–21.548 | 50 |
| E5 600 / volatile Update | ms | 21.897 [21.794, 22.025] | 21.897–21.897 | 50 |
| E5 1,000 / volatile Read | ms | 33.608 [33.457, 33.768] | 33.608–33.608 | 50 |
| E5 1,000 / volatile Update | ms | 34.239 [34.017, 34.386] | 34.239–34.239 | 50 |
| E5 1,105 / volatile Read | ms | 36.955 [36.750, 37.088] | 36.955–36.955 | 50 |
| E5 1,105 / volatile Update | ms | 37.484 [37.298, 37.642] | 37.484–37.484 | 50 |
| E5 1,105 / volatile first-key Read | ms | 36.917 [36.746, 37.098] | 36.917–36.917 | 50 |
| E5 10 / durable Read | ms | 3.820 [3.792, 3.863] | 3.820–3.820 | 50 |
| E5 10 / durable Update | ms | 16.489 [11.932, 16.939] | 16.489–16.489 | 50 |
| E5 10 / durable first-key Read | ms | 3.819 [3.764, 3.867] | 3.819–3.819 | 50 |
| E5 30 / durable Read | ms | 4.523 [4.482, 4.553] | 4.523–4.523 | 50 |
| E5 30 / durable Update | ms | 15.808 [13.785, 16.388] | 15.808–15.808 | 50 |
| E5 100 / durable Read | ms | 6.599 [6.523, 6.678] | 6.599–6.599 | 50 |
| E5 100 / durable Update | ms | 17.768 [14.500, 19.560] | 17.768–17.768 | 50 |
| E5 300 / durable Read | ms | 12.578 [12.499, 12.641] | 12.578–12.578 | 50 |
| E5 300 / durable Update | ms | 23.688 [21.789, 25.607] | 23.688–23.688 | 50 |
| E5 600 / durable Read | ms | 21.638 [21.565, 21.750] | 21.638–21.638 | 50 |
| E5 600 / durable Update | ms | 32.905 [31.713, 34.006] | 32.905–32.905 | 50 |
| E5 1,000 / durable Read | ms | 33.689 [33.547, 33.826] | 33.689–33.689 | 50 |
| E5 1,000 / durable Update | ms | 45.334 [44.508, 46.284] | 45.334–45.334 | 50 |
| E5 1,105 / durable Read | ms | 36.970 [36.840, 37.194] | 36.970–36.970 | 50 |
| E5 1,105 / durable Update | ms | 49.053 [48.235, 50.335] | 49.053–49.053 | 50 |
| E5 1,105 / durable first-key Read | ms | 37.152 [36.930, 37.299] | 37.152–37.152 | 50 |

## Registration (nine observations per condition)

| Program / storage | Min (s) | Median (s) | Max (s) | Session median min–max (s) | n |
|---|---|---|---|---|---|
| Read / volatile | 6.67 | 6.74 | 6.85 | 6.68–6.74 | 9 |
| Indexed / volatile | 11.43 | 11.49 | 11.50 | 11.44–11.50 | 9 |
| Voucher / volatile | 10.84 | 10.87 | 10.95 | 10.84–10.92 | 9 |
| Read / durable | 6.67 | 6.72 | 6.82 | 6.68–6.73 | 9 |
| Indexed / durable | 11.44 | 11.50 | 11.58 | 11.49–11.51 | 9 |
| Voucher / durable | 10.79 | 10.87 | 11.03 | 10.85–10.87 | 9 |

## Ordinary phases

| Program | Phase | Median [Q1,Q3] (ms) | n |
|---|---|---|---|
| Read | Admission wall | 4,902.89 [4,891.20, 4,925.59] | 30 |
| Read | Checking (overlaps build) | 2,946.81 [2,939.82, 2,953.10] | 30 |
| Read | C generation/build (overlaps checking) | 1,972.25 [1,969.02, 1,980.94] | 30 |
| Read | Worker | 9.95 [9.90, 9.99] | 30 |
| Indexed | Admission wall | 8,826.82 [8,812.15, 8,846.83] | 30 |
| Indexed | Checking (overlaps build) | 5,443.76 [5,418.40, 5,457.10] | 30 |
| Indexed | C generation/build (overlaps checking) | 4,364.81 [4,353.06, 4,379.47] | 30 |
| Indexed | Worker | 15.80 [15.73, 15.88] | 30 |
| Voucher | Admission wall | 9,102.07 [9,082.17, 9,129.50] | 30 |
| Voucher | Checking (overlaps build) | 6,047.32 [6,024.68, 6,074.25] | 30 |
| Voucher | C generation/build (overlaps checking) | 4,760.70 [4,730.68, 4,777.82] | 30 |
| Voucher | Worker | 21.47 [19.00, 23.72] | 30 |

## Preparation break-even

| Program | Calls |
|---|---|
| Read | 2 |
| Indexed | 2 |
| Voucher | 2 |

## E3 ordinary context (10 total rows)

| Policy / operation | Median [Q1,Q3] (s) | n |
|---|---|---|
| Point / read | 4.908 [4.899, 4.916] | 30 |
| Point / update | 5.119 [5.100, 5.142] | 30 |
| Owner / read | 10.495 [10.481, 10.511] | 30 |
| Owner / update | 12.287 [12.267, 12.304] | 30 |

## Fixed-clock verification times

| Command | Seconds | n | Exit |
|---|---|---|---|
| make verify-contract | 63.108 | 1 | 0 |
| make verify | 788.312 | 1 | 0 |
| make test | 677.565 | 1 | 0 |

Quartiles and session spread are undefined for these single fixed-clock command observations. Checking and C generation/build diagnostics overlap inside admission wall time; they must not be added to it or to each other.

## Verification inventory

| Fact | Count |
|---|---|
| NegativeFixtures | 397 |
| ContractTheoremTypes | 15 |
| ProofLawDeclarations | 1,142 |
| ProofDefinitions | 2,221 |
| ProofTheoremWitnesses | 14 |
| PublicTheoremWitnesses | 17 |
| RlsNegativeFixtures | 12 |
| RlsNativeResponses | 253 |
| HostDutyCount | 8 |

The core and RLS negative-fixture counts are separate; every fixture is checked in both official modes. The eight numbered T3 items regroup the previous eleven obligations and do not imply reduced trust.

## Source inventory

Nonblank physical lines, including comments/imports/attributes. Rust: server/*.rs; #[cfg(test)] attribute and following top-level item through its unindented closing brace are test lines; all remaining lines are production. Client ratios count Client.bend (plus Voucher.bend for the voucher dispatcher) versus its local certificate/checked-action/completion files only, excluding reusable library, domain/model, configuration, seed, and separately checked functional proofs.

| Area | Program / production lines | Proof / test lines | Proof/program ratio |
|---|---|---|
| Rust host | 1,971 | 1,435 | — |
| Indexed | 46 | 404 | 8.783 |
| Voucher | 119 | 205 | 1.723 |
| Rls | 126 | 355 | 2.817 |

| Source area | Files | Nonblank lines |
|---|---|---|
| Src | 22 | 2,058 |
| Contract | 19 | 2,671 |
| Proof | 142 | 28,486 |
| Server | 5 | 3,406 |
| Tools | 9 | 1,428 |
| Native | 2 | 93 |
| Rls | 9 | 1,268 |

## New macro contract

| Macro | Value | Unit |
|---|---|---|
| `\CpuGovernor` | performance | text |
| `\CpuClockGHz` | 3.6 | GHz |
| `\TurboSetting` | disabled | text |
| `\SessionCount` | 3 | sessions |
| `\RustProductionLines` | 1,971 | lines |
| `\RustTestLines` | 1,435 | lines |
| `\IndexedClientLines` | 46 | lines |
| `\IndexedProofLines` | 404 | lines |
| `\IndexedProofRatio` | 8.78261 | ratio |
| `\VoucherClientLines` | 119 | lines |
| `\VoucherProofLines` | 205 | lines |
| `\VoucherProofRatio` | 1.72269 | ratio |
| `\RlsClientLines` | 126 | lines |
| `\RlsProofLines` | 355 | lines |
| `\RlsProofRatio` | 2.81746 | ratio |
| `\RlsNonblankLines` | 1,268 | lines |
| `\RlsNegativeFixtures` | 12 | fixtures |
| `\RlsNativeResponses` | 253 | responses |
| `\HostDutyCount` | 8 | duties |
| `\ComparisonLargeRows` | 1,104 | rows |
| `\ScalingFirstKeySmallMs` | 3.85053 | ms |
| `\ScalingFirstKeyLargeMs` | 36.9168 | ms |
| `\LargeJayReadMs` | 36.7793 | ms |
| `\LargeJayWriteMs` | 48.9432 | ms |
| `\LargePgReadMs` | 0.04194 | ms |
| `\LargePgWriteMs` | 2.74506 | ms |
| `\LargeSqReadMs` | 0.003227 | ms |
| `\LargeSqWriteMs` | 2.95485 | ms |
| `\LargeOwnerJayReadMs` | 37.8567 | ms |
| `\LargeOwnerJayWriteMs` | 50.1313 | ms |
| `\LargeOwnerPgReadMs` | 0.0423225 | ms |
| `\LargeOwnerPgWriteMs` | 3.25858 | ms |
| `\LargeOwnerSqReadMs` | 0.003377 | ms |
| `\LargeOwnerSqWriteMs` | 3.16312 | ms |

## Observations and limits

Fixed-clock volatile last-key read is 3.854 ms at 10 rows and 6.554 ms at 100 rows (1.700×). Compare the earlier powersave measurements in performance-report.txt; the fresh data are not pooled with that historical run.

At 1,105 rows, volatile first-key read is 36.917 ms versus 36.955 ms for last-key read. Their similar costs show that lookup position does not account for most observed scaling. Complete-state transfer, decoding, validation and publication remain inside the timing boundary; this comparison does not isolate copying alone.

Durable Indexed session medians (ms): 17.169, 17.526, 16.777. Publication phase medians: 10.697, 11.327, 10.556. Worker phase medians: 3.718, 3.689, 3.691. The fixed policy does not eliminate publication variability; these observations do not isolate individual fsync calls. No slow session was removed.

## Run note

All E1–E5 datasets were refreshed after integrating checked host error replies, overlapped admission/build and unbounded RLS. E1–E3 retain three independent sessions; E5 retains its one-session scaling protocol. Complete command output and exact CPU restoration receipts are retained.

The initial aggregate test failed because its RLS diagnostic counter also counted checked-denial memo/controller logs. The counter now matches actual PRIMARY_CHECK error headers and requires exactly one false-proof location per negative. The failed command/output is retained in validation-attempts.json; the successful rerun supplies the E4 test wall time.

## CPU restoration

Final observed values (all 16 CPUs): governor `powersave`; EPP `balance_performance`; `intel_pstate/no_turbo=0`. Exact saved settings and final sampled frequencies are in `cpu-restoration.json`. Verified: True.

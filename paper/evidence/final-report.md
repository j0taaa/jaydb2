# Final controlled JayDB2 thesis evidence

Branch: `t3/paper-gpu-simulation`. Engine source SHA-256: `21faf2216e31b895ce17d4918f7746c392079d5ef3d543e75938cc9b5143eb3b`; executable SHA-256: `d0b11273de3e0a50ffffaa062da49dc334959f959a4c3107fbcdddd289d0416c`. Raw metadata retain each invocation commit; all refreshed E1–E6 datasets and the focused GPU benchmark must have identical engine fingerprints.

E1–E3: three fresh sessions per condition. E5: one session, one service per storage mode reused across all sizes. Governor/EPP performance; turbo disabled; nominal 3.6 GHz. No CPU pinning. Inclusive quartiles; no outlier removal.

E3 uses 10 and 1,104 total rows in all engines; owner rows are divided equally between Alice and Bob. SQLite is unconstrained. E4 commands were rerun under the same fixed-clock policy; each wall time is one observation.

All latency rows below use milliseconds. Session spread is min–max of session medians; E5 has only one session. Throughput rows use calls/s.

| Metric | Unit | Pooled median [Q1, Q3] | Session median min–max | n |
|---|---|---|---|---|
| E1 Read | ms | 4,931.947 [4,920.047, 4,943.551] | 4,924.770–4,938.016 | 30 |
| E1 Indexed | ms | 8,888.189 [8,868.921, 8,955.456] | 8,875.383–8,908.631 | 30 |
| E1 Voucher | ms | 9,154.454 [9,125.669, 9,182.382] | 9,148.035–9,165.637 | 30 |
| E2 Read / volatile | ms | 3.916 [3.867, 3.963] | 3.909–3.926 | 900 |
| E2 Read / volatile active throughput | calls/s | 254.996 [254.273, 256.112] | 254.094–255.480 | 30 |
| E2 Read / volatile closed-loop throughput | calls/s | 250.751 [249.047, 250.825] | 247.344–250.898 | 3 |
| E2 Indexed / volatile | ms | 6.015 [5.947, 6.093] | 5.985–6.079 | 900 |
| E2 Indexed / volatile active throughput | calls/s | 166.441 [165.578, 167.101] | 165.585–166.747 | 30 |
| E2 Indexed / volatile closed-loop throughput | calls/s | 164.116 [159.592, 164.132] | 155.068–164.149 | 3 |
| E2 Voucher / volatile | ms | 6.165 [6.104, 6.246] | 6.153–6.183 | 900 |
| E2 Voucher / volatile active throughput | calls/s | 162.352 [160.547, 162.621] | 161.764–162.578 | 30 |
| E2 Voucher / volatile closed-loop throughput | calls/s | 78.050 [77.115, 78.867] | 76.180–79.685 | 3 |
| E2 Read / durable | ms | 3.919 [3.875, 3.962] | 3.911–3.925 | 900 |
| E2 Read / durable active throughput | calls/s | 254.748 [253.971, 255.490] | 254.486–255.085 | 30 |
| E2 Read / durable closed-loop throughput | calls/s | 250.330 [250.241, 250.386] | 250.153–250.441 | 3 |
| E2 Indexed / durable | ms | 17.162 [15.409, 18.367] | 17.146–17.446 | 900 |
| E2 Indexed / durable active throughput | calls/s | 58.769 [57.835, 59.384] | 57.566–59.482 | 30 |
| E2 Indexed / durable closed-loop throughput | calls/s | 58.083 [57.585, 58.581] | 57.087–59.079 | 3 |
| E2 Voucher / durable | ms | 18.184 [17.046, 48.242] | 17.212–56.043 | 900 |
| E2 Voucher / durable active throughput | calls/s | 55.172 [20.643, 58.080] | 16.892–58.070 | 30 |
| E2 Voucher / durable closed-loop throughput | calls/s | 28.536 [18.582, 28.588] | 8.627–28.639 | 3 |
| E3 10 Point PostgreSQL Read | ms | 0.042 [0.041, 0.043] | 0.041–0.042 | 900 |
| E3 10 Point PostgreSQL Update | ms | 2.418 [2.195, 3.548] | 2.241–3.398 | 900 |
| E3 10 Point SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 10 Point SQLite Update | ms | 6.752 [4.590, 7.204] | 5.898–6.998 | 900 |
| E3 10 Point JayDB2 Read | ms | 3.855 [3.812, 3.921] | 3.836–3.884 | 900 |
| E3 10 Point JayDB2 Update | ms | 14.644 [13.719, 15.863] | 14.338–14.831 | 900 |
| E3 10 Owner PostgreSQL Read | ms | 0.042 [0.042, 0.043] | 0.042–0.042 | 900 |
| E3 10 Owner PostgreSQL Update | ms | 3.260 [2.221, 3.446] | 2.951–3.285 | 900 |
| E3 10 Owner SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 10 Owner SQLite Update | ms | 5.659 [4.638, 6.730] | 5.616–5.732 | 900 |
| E3 10 Owner JayDB2 Read | ms | 5.072 [5.020, 5.120] | 5.062–5.076 | 900 |
| E3 10 Owner JayDB2 Update | ms | 15.903 [14.679, 17.464] | 15.745–16.838 | 900 |
| E3 1,104 Point PostgreSQL Read | ms | 0.042 [0.042, 0.043] | 0.042–0.043 | 900 |
| E3 1,104 Point PostgreSQL Update | ms | 3.058 [2.269, 3.466] | 2.637–3.275 | 900 |
| E3 1,104 Point SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 1,104 Point SQLite Update | ms | 2.527 [2.079, 3.307] | 2.527–2.851 | 900 |
| E3 1,104 Point JayDB2 Read | ms | 36.863 [36.709, 37.042] | 36.813–36.911 | 900 |
| E3 1,104 Point JayDB2 Update | ms | 48.862 [47.761, 49.890] | 48.677–48.980 | 900 |
| E3 1,104 Owner PostgreSQL Read | ms | 0.043 [0.042, 0.044] | 0.042–0.043 | 900 |
| E3 1,104 Owner PostgreSQL Update | ms | 3.324 [2.229, 3.468] | 2.959–3.331 | 900 |
| E3 1,104 Owner SQLite Read | ms | 0.003 [0.003, 0.003] | 0.003–0.003 | 900 |
| E3 1,104 Owner SQLite Update | ms | 2.956 [2.130, 3.443] | 2.545–3.158 | 900 |
| E3 1,104 Owner JayDB2 Read | ms | 37.876 [37.703, 38.062] | 37.792–37.956 | 900 |
| E3 1,104 Owner JayDB2 Update | ms | 50.503 [49.026, 57.073] | 49.585–95.333 | 900 |
| E5 10 / volatile Read | ms | 3.871 [3.839, 3.901] | 3.871–3.871 | 50 |
| E5 10 / volatile Update | ms | 3.897 [3.866, 3.934] | 3.897–3.897 | 50 |
| E5 10 / volatile first-key Read | ms | 3.902 [3.854, 3.936] | 3.902–3.902 | 50 |
| E5 30 / volatile Read | ms | 4.484 [4.452, 4.525] | 4.484–4.484 | 50 |
| E5 30 / volatile Update | ms | 4.528 [4.484, 4.570] | 4.528–4.528 | 50 |
| E5 100 / volatile Read | ms | 6.566 [6.479, 6.629] | 6.566–6.566 | 50 |
| E5 100 / volatile Update | ms | 6.612 [6.561, 6.656] | 6.612–6.612 | 50 |
| E5 300 / volatile Read | ms | 12.545 [12.458, 12.690] | 12.545–12.545 | 50 |
| E5 300 / volatile Update | ms | 12.732 [12.659, 12.847] | 12.732–12.732 | 50 |
| E5 600 / volatile Read | ms | 21.697 [21.576, 21.838] | 21.697–21.697 | 50 |
| E5 600 / volatile Update | ms | 21.988 [21.902, 22.184] | 21.988–21.988 | 50 |
| E5 1,000 / volatile Read | ms | 33.864 [33.658, 33.988] | 33.864–33.864 | 50 |
| E5 1,000 / volatile Update | ms | 34.262 [34.168, 34.483] | 34.262–34.262 | 50 |
| E5 1,105 / volatile Read | ms | 37.054 [36.905, 37.253] | 37.054–37.054 | 50 |
| E5 1,105 / volatile Update | ms | 37.703 [37.478, 37.896] | 37.703–37.703 | 50 |
| E5 1,105 / volatile first-key Read | ms | 37.001 [36.851, 37.171] | 37.001–37.001 | 50 |
| E5 10 / durable Read | ms | 3.882 [3.847, 3.932] | 3.882–3.882 | 50 |
| E5 10 / durable Update | ms | 14.574 [14.408, 14.691] | 14.574–14.574 | 50 |
| E5 10 / durable first-key Read | ms | 3.867 [3.824, 3.939] | 3.867–3.867 | 50 |
| E5 30 / durable Read | ms | 4.499 [4.458, 4.555] | 4.499–4.499 | 50 |
| E5 30 / durable Update | ms | 15.595 [13.875, 25.727] | 15.595–15.595 | 50 |
| E5 100 / durable Read | ms | 6.584 [6.516, 6.630] | 6.584–6.584 | 50 |
| E5 100 / durable Update | ms | 17.559 [15.830, 18.418] | 17.559–17.559 | 50 |
| E5 300 / durable Read | ms | 12.553 [12.483, 12.654] | 12.553–12.553 | 50 |
| E5 300 / durable Update | ms | 23.593 [20.827, 25.460] | 23.593–23.593 | 50 |
| E5 600 / durable Read | ms | 21.586 [21.469, 21.720] | 21.586–21.586 | 50 |
| E5 600 / durable Update | ms | 33.455 [31.915, 34.307] | 33.455–33.455 | 50 |
| E5 1,000 / durable Read | ms | 33.849 [33.731, 33.974] | 33.849–33.849 | 50 |
| E5 1,000 / durable Update | ms | 45.790 [44.690, 46.968] | 45.790–45.790 | 50 |
| E5 1,105 / durable Read | ms | 37.023 [36.831, 37.227] | 37.023–37.023 | 50 |
| E5 1,105 / durable Update | ms | 49.275 [47.907, 50.180] | 49.275–49.275 | 50 |
| E5 1,105 / durable first-key Read | ms | 37.122 [36.953, 37.242] | 37.122–37.122 | 50 |

## Registration (nine observations per condition)

| Program / storage | Min (s) | Median (s) | Max (s) | Session median min–max (s) | n |
|---|---|---|---|---|---|
| Read / volatile | 6.75 | 6.76 | 6.87 | 6.76–6.77 | 9 |
| Indexed / volatile | 11.49 | 11.52 | 11.60 | 11.50–11.53 | 9 |
| Voucher / volatile | 10.85 | 10.89 | 11.02 | 10.87–10.96 | 9 |
| Read / durable | 6.69 | 6.74 | 6.78 | 6.73–6.75 | 9 |
| Indexed / durable | 11.50 | 11.53 | 11.60 | 11.52–11.53 | 9 |
| Voucher / durable | 10.85 | 10.92 | 11.05 | 10.89–10.94 | 9 |

## Ordinary phases

| Program | Phase | Median [Q1,Q3] (ms) | n |
|---|---|---|---|
| Read | Admission wall | 4,919.11 [4,907.50, 4,931.24] | 30 |
| Read | Checking (overlaps build) | 2,956.76 [2,945.25, 2,969.25] | 30 |
| Read | C generation/build (overlaps checking) | 1,976.00 [1,971.82, 1,980.99] | 30 |
| Read | Worker | 9.93 [9.88, 10.00] | 30 |
| Indexed | Admission wall | 8,868.65 [8,849.32, 8,935.78] | 30 |
| Indexed | Checking (overlaps build) | 5,469.82 [5,445.66, 5,501.22] | 30 |
| Indexed | C generation/build (overlaps checking) | 4,389.29 [4,378.50, 4,402.94] | 30 |
| Indexed | Worker | 15.89 [15.79, 15.98] | 30 |
| Voucher | Admission wall | 9,126.19 [9,099.53, 9,158.15] | 30 |
| Voucher | Checking (overlaps build) | 6,066.39 [6,043.11, 6,106.11] | 30 |
| Voucher | C generation/build (overlaps checking) | 4,766.16 [4,726.87, 4,780.08] | 30 |
| Voucher | Worker | 21.35 [18.89, 23.80] | 30 |

## Preparation break-even

| Program | Calls |
|---|---|
| Read | 2 |
| Indexed | 2 |
| Voucher | 2 |

## E3 ordinary context (10 total rows)

| Policy / operation | Median [Q1,Q3] (s) | n |
|---|---|---|
| Point / read | 4.923 [4.915, 4.935] | 30 |
| Point / update | 5.140 [5.122, 5.187] | 30 |
| Owner / read | 10.502 [10.481, 10.524] | 30 |
| Owner / update | 12.298 [12.275, 12.316] | 30 |

## Fixed-clock verification times

| Command | Seconds | n | Exit |
|---|---|---|---|
| make verify-contract | 62.879 | 1 | 0 |
| make verify | 794.372 | 1 | 0 |
| make test | 710.082 | 1 | 0 |

Quartiles and session spread are undefined for these single fixed-clock command observations. Checking and C generation/build diagnostics overlap inside admission wall time; they must not be added to it or to each other.

## Verification inventory

| Fact | Count |
|---|---|
| NegativeFixtures | 402 |
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
| Rust host | 2,047 | 1,519 | — |
| Indexed | 46 | 404 | 8.783 |
| Voucher | 119 | 205 | 1.723 |
| Rls | 126 | 355 | 2.817 |

| Source area | Files | Nonblank lines |
|---|---|---|
| Src | 22 | 2,058 |
| Contract | 19 | 2,671 |
| Proof | 142 | 28,486 |
| Server | 5 | 3,566 |
| Tools | 9 | 1,483 |
| Native | 2 | 93 |
| Rls | 9 | 1,268 |

## New macro contract

| Macro | Value | Unit |
|---|---|---|
| `\CpuGovernor` | performance | text |
| `\CpuClockGHz` | 3.6 | GHz |
| `\TurboSetting` | disabled | text |
| `\SessionCount` | 3 | sessions |
| `\RustProductionLines` | 2,047 | lines |
| `\RustTestLines` | 1,519 | lines |
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
| `\ScalingFirstKeySmallMs` | 3.90192 | ms |
| `\ScalingFirstKeyLargeMs` | 37.0005 | ms |
| `\LargeJayReadMs` | 36.8626 | ms |
| `\LargeJayWriteMs` | 48.8624 | ms |
| `\LargePgReadMs` | 0.042018 | ms |
| `\LargePgWriteMs` | 3.05823 | ms |
| `\LargeSqReadMs` | 0.003242 | ms |
| `\LargeSqWriteMs` | 2.52682 | ms |
| `\LargeOwnerJayReadMs` | 37.8761 | ms |
| `\LargeOwnerJayWriteMs` | 50.5033 | ms |
| `\LargeOwnerPgReadMs` | 0.042818 | ms |
| `\LargeOwnerPgWriteMs` | 3.32408 | ms |
| `\LargeOwnerSqReadMs` | 0.003351 | ms |
| `\LargeOwnerSqWriteMs` | 2.95575 | ms |

## Observations and limits

Fixed-clock volatile last-key read is 3.871 ms at 10 rows and 6.566 ms at 100 rows (1.696×). Compare the earlier powersave measurements in performance-report.txt; the fresh data are not pooled with that historical run.

At 1,105 rows, volatile first-key read is 37.001 ms versus 37.054 ms for last-key read. Their similar costs show that lookup position does not account for most observed scaling. Complete-state transfer, decoding, validation and publication remain inside the timing boundary; this comparison does not isolate copying alone.

Durable Indexed session medians (ms): 17.146, 17.446, 17.204. Publication phase medians: 10.824, 10.807, 11.020. Worker phase medians: 3.700, 3.699, 3.687. The fixed policy does not eliminate publication variability; these observations do not isolate individual fsync calls. No slow session was removed.

## Run note

All E1–E6 datasets and the focused GPU benchmark were refreshed on the frozen opt-in GPU/simulation engine. E1–E3 retain three independent sessions; E5 retains its one-session scaling protocol. Complete command output and exact CPU restoration receipts are retained.

Historical validation-attempts.json retains an earlier RLS diagnostic-counter failure and its output. That development record does not supply the current E4 timings; all three current commands were freshly executed on the frozen engine.

## CPU restoration

Final observed values (all 16 CPUs): governor `powersave`; EPP `balance_performance`; `intel_pstate/no_turbo=0`. Exact saved settings and final sampled frequencies are in `cpu-restoration.json`. Verified: True.

## E6 certified simulation

Measured revision `2f768bb83c9a42ca9cb2f72faf49e2d75c8ca6ec`; `dirty: []`.
Engine source SHA-256 `21faf2216e31b895ce17d4918f7746c392079d5ef3d543e75938cc9b5143eb3b`; executable SHA-256 `d0b11273de3e0a50ffffaa062da49dc334959f959a4c3107fbcdddd289d0416c`.

Generated by `paper/evidence.py` from retained raw samples after validation. E6 and E1–E5 share engine fingerprints with the focused GPU benchmark.

[Application arithmetic and certificate](../../applications/simulation/README.md); [timing harness](../bench/simulation.py).

The universal certificate confines scenario reads and result writes to the authenticated user and proves finite Action execution; structural checking covers numerical recursion. It does not prove numeric/statistical properties or CUDA correctness. A foreign-result-write negative fails the installed access obligation in both official modes.

Complete request/query wall time in milliseconds: median (min–max), 1 excluded warmup and 3 measured samples per completed cell. Preparation is separate.

| Paths × steps | JayDB2 CPU-1 | JayDB2 CPU-16 | JayDB2 CUDA | PostgreSQL PL/pgSQL | SQLite CTE |
|---|---:|---:|---:|---:|---:|
| 4 × 32 | 6.678 (6.588–6.964) | 7.063 (6.830–7.183) | 161.451 (149.429–169.164) | 0.183 (0.115–0.261) | 0.074 (0.072–0.074) |
| 1,024 × 256 | 7.144 (7.108–7.185) | 7.151 (7.107–7.184) | 155.400 (155.209–175.475) | 29.339 (29.323–29.438) | 162.435 (161.235–162.778) |
| 16,384 × 1,024 | 34.946 (34.903–35.179) | 10.608 (10.591–10.790) | 168.740 (162.294–170.678) | 1847.875 (1845.225–1850.114) | timeout 10 s |
| 65,536 × 16,384 | 1802.224 (1802.072–1802.405) | 234.767 (234.621–234.930) | 178.204 (177.822–181.845) | timeout 10 s | not run |

## Preparation (one observation, excluded above)

| Backend | ms |
|---|---:|
| cpu-1 | 8651.317 |
| cpu-16 | 8615.030 |
| cuda | 11764.108 |

## Protocol and limitations

- JayDB2 RAM state, PostgreSQL temporary tables (no table WAL), SQLite :memory:; no durability comparison.
- JayDB2 fresh child per request, fresh authentication, integrity checks and complete publication; proof admission timed separately.
- SQL execute/fetch includes parameter reads, simulation, upsert and returning all aggregates; no host-language UDF.
- SQL is an arithmetic baseline without equivalent proof admission or authentication/RLS.
- PostgreSQL PL/pgSQL is interpreted; SQLite recursive CTE is not designed for heavy numerical compute.
- One session, one excluded warmup and at least three samples per measured size; complete state checked outside timing.
- CPU clock policy fixed by wrapper; GPU clock unfixed and device drives desktop; no general speedup claim.
- SQL statement timeout 10s; later sizes not run after first timeout; no extrapolation.

CPU restoration is verified after every benchmark and in `cpu-restoration.json`/`refresh-log.json`. GPU clocks are unfixed. Artifact reports retain resolved CUDA library paths/hashes, not pinned library guarantees.

Independent scalar/NumPy oracles check every completed size and complete state. SQL controls exercise both users; timeouts retain cancellation diagnostics and rollback is checked by the harness. Timeouts and subsequent unrun sizes supply neither results nor extrapolated timing.

[Raw evidence](simulation.json); [standalone figure](simulation.svg). Historical launch/development logs in `simulation-launch.json`, `simulation-validation.json` and `simulation-development.json` describe earlier revisions; they are not fresh E6 timings.

## Focused GPU benchmark

Measured revision `2f768bb83c9a42ca9cb2f72faf49e2d75c8ca6ec`; `dirty: []`.
Engine source SHA-256 `21faf2216e31b895ce17d4918f7746c392079d5ef3d543e75938cc9b5143eb3b`; executable SHA-256 `d0b11273de3e0a50ffffaa062da49dc334959f959a4c3107fbcdddd289d0416c`.

Generated by `paper/evidence.py` from the current raw JSON, sharing engine fingerprints with E1–E6. CPU is the default; explicit bang calls opt into official Bend CUDA execution.

Both official checkers accept the same sealed Book before CUDA C emission/compilation/prebuild. Proofs concern that Book’s semantics, under identical certificate, termination, access/RLS, size and publication obligations. No GPU validity axiom is introduced.

T2 additionally trusts Bend’s emitted CUDA runtime, NVRTC, CUDA driver, managed memory and GPU hardware. CUDA headers/libraries come from the host environment; resolved library paths/hashes are recorded, not pinned. Differential tests/oracles are implementation evidence, not proof of CUDA correctness.

Reports bind emitted C, executable and cubin hashes. CUDA execution rechecks artifacts before launch and accepting output; prepared calls compare exact sealed bytes. Artifact changes, rebuild notices and device errors discard the proposal. Requested bangs have no CPU fallback. Execution is serial per instance.

Native-worker and complete-request columns are separate trials, not additive phases. Each excludes one warmup and retains 3 samples. Worker times include fresh process/device startup and exit; requests also include authentication, integrity checking, publication/inspector emission and decoding.

| Depth / mixing rounds | Backend | Native worker median (range), ms | Complete request median (range), ms |
|---|---|---:|---:|
| 2 / 32,768 | cpu-1 | 3.312 (3.290–3.407) | 5.658 (5.563–5.750) |
| 16 / 4,294,967,296 | cpu-1 | 7179.926 (7179.800–7179.941) | 7182.741 (7182.451–7183.980) |
| 2 / 32,768 | cpu-16 | 3.725 (3.638–3.758) | 6.296 (6.037–6.371) |
| 16 / 4,294,967,296 | cpu-16 | 499.232 (472.148–499.361) | 496.305 (475.285–502.027) |
| 2 / 32,768 | cuda | 175.133 (171.021–180.018) | 159.885 (148.233–160.458) |
| 16 / 4,294,967,296 | cuda | 216.248 (210.000–217.305) | 205.837 (205.350–209.966) |

## Separate preparation

| Backend | ms (one observation) |
|---|---:|
| cpu-1 | 8139.450 |
| cpu-16 | 8102.887 |
| cuda | 11201.489 |

The independent Python/NumPy U32 oracle performs every seed/round and a small scalar cross-check. Every native proposal and complete published state is checked, including Bob’s unchanged credential. All modes emit identical C. Benchmarks use the unwrapped real driver.

CPU policy is fixed and restored after each benchmark; GPU clock is unfixed and the device drives the desktop. Fresh process/device costs dominate small work. No kernel-only latency, general speedup, timeout/resource quota, persistent worker, cross-instance scheduling or portability guarantee follows. The corpus does not cap total driver memory, and integrity checks do not defeat hostile same-UID file-use races.

[Raw samples and artifact/library hashes](gpu-programs.json); [standalone figure](gpu-programs.svg). Historical implementation/launch validation is retained in `gpu-validation.json` and `gpu-validation-rerun.json`; those records identify their own earlier revisions and are not current paper measurements.

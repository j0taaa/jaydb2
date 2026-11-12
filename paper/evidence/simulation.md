# Certified table-driven simulation

Measured revision `6ef0194eb5bedbdfb9605927b92a45c48b0ee335`. Dirty paths at measurement are retained in the raw metadata. This evidence is separate from the thesis E1–E5 dataset; no main/slides or contract files changed.

The application reads the authenticated user’s seed, drift and volatility from three cells in `scenarios`, then writes `sum`, `max`, `above`, and `paths` to that user’s `results` row. Two scenario rows keep access/state overhead small while runtime `[depth, steps]` controls numerical work.

For path `i`, start `r = (seed + i*747796405) & 0xffffffff`, `v = 1000000`. Each step computes `r = (r*1664525 + 1013904223) & 0xffffffff`, then `v = (v + drift%65536 + ((r>>16)%(2*(volatility%32768)+1)) - volatility%32768) & 0xffffffff`. The balanced tree launches one `simulate!` call and reduces terminal values: modular U32 sum, unsigned maximum, count strictly above 1,000,000, and path count. This integer random walk is a reproducible Monte Carlo compute example, not a calibrated pricing model or a statistically validated PRNG.

The universal certificate proves own-scenario reads and own-result writes at every prefix and outcome, including failed operations and refusals. The `Safe` induction and `T.program_finite` prove a finite five-constructor Action chain on arbitrary states; the official checker checks numerical recursion structurally. The standard finalizer retains canonical structure and state/response limits. No new axiom or proof shortcut was added. The certificate does not prove the numeric checksum or CUDA/compiler correctness; independent scalar Python and NumPy check every path/step. The rejected `SimulationUnauthorizedWrite` fixture checks the exact installed access obligation and must fail only at `false` in both official modes.

## Complete request/query timings

Milliseconds: median (minimum–maximum), one excluded warmup and three measured samples. Preparation is excluded and listed separately. JayDB2 intervals include request encoding/transport, fresh authentication, exact prepared-artifact checks, fresh native child/device startup, simulation, writing results, publication, response decoding and administrator feed emission. SQL intervals include execute/fetch, in-database parameter reads, computation, aggregate upsert and returned statistics. Complete-state checks run outside the measured interval.

| Paths × steps | JayDB2 CPU 1 | JayDB2 CPU 16 | JayDB2 CUDA | PostgreSQL | SQLite |
| --- | ---: | ---: | ---: | ---: | ---: |
| 4 × 32 | 6.689 (6.629–6.891) | 6.938 (6.827–7.096) | 167.810 (164.972–172.073) | 0.119 (0.107–0.195) | 0.074 (0.073–0.076) |
| 1,024 × 256 | 7.060 (6.990–7.191) | 7.158 (6.935–7.293) | 164.805 (159.266–174.970) | 29.438 (29.379–29.478) | 161.111 (160.890–161.379) |
| 16,384 × 1,024 | 35.350 (35.104–35.452) | 11.231 (10.780–11.348) | 165.424 (157.320–169.135) | 1848.718 (1848.689–1855.158) | timeout 10 s |
| 65,536 × 16,384 | 1805.489 (1803.301–1807.990) | 245.043 (236.955–248.308) | 190.959 (172.806–194.872) | timeout 10 s | not run beyond 262144 updates |

PostgreSQL completed through 16,777,216 updates; its 1,073,741,824-update query timed out at 10 seconds. SQLite completed through 262,144 updates; its 16,777,216-update query timed out, and no larger SQLite size was run. The sweep retained 51 measured samples and 17 warmups; neither timeout supplies a result or an extrapolated timing.

Preparation/admission (one observation, both checkers, compilation and optional CUDA prebuild): cpu-1: 8565.895 ms; cpu-16: 8636.227 ms; cuda: 11928.167 ms.

[Raw samples, oracle outputs, full JayDB2 states, settings and hashes](simulation.json). [Standalone median/range figure](simulation.svg). SQL timeouts are observed cancellations; later sizes are explicitly not run. No timings or results beyond the cap are extrapolated.

## Validation

| Locked command | Result | Seconds |
| --- | --- | ---: |
| `make build` | PASS | 0.020 |
| `make verify` | PASS | 703.264 |
| `make test` | PASS | 593.582 |
| `make test-gpu` | PASS | 279.674 |
| `make benchmark-simulation` | PASS | 115.113 |
| `python3 -m pytest paper/test_evidence.py` | PASS | 16.038 |

[Validation logs: hashes and output tails](simulation-validation.json). Full logs stay in the ignored `.build/simulation/validation/` directory. The initial development application check failed on a two-scrutinee fallback written with one pattern; the next application attempt found that a nested-pattern exclusion did not reduce in a dependent proof. A parsed-size datatype with explicit constructor cases corrected that issue. SQLite scalar-oracle checks passed in both failed application attempts. A later observer expectation was corrected to validate metadata snapshots against the previous root and compare initialized/completed publications. [Development failure logs](simulation-development.json) are retained; failed attempts are not counted as successful validation.

Verification passed all positive roots and 401 negative fixtures / 802 exact-`false` rejections. `make test` passed 2 simulation tests, 47 admission/verifier tests, 10 native tests, 39 Rust tests, 16 service integration tests, and 253 RLS responses with 12 admission denials. The CUDA suite passed 7 methods; the evidence suite passed 33 tests.

[Real launch attestation](simulation-launch.json) records 20 successful launches, 12 synchronizations and `BANGS=1` for emitted C SHA-256 `e3c83426f36a86f6a2ec325828b76ef2acc7cbdd6e2aa78d3f92884fd46f3888`, identical in all three benchmark artifacts. Timing runs use the unwrapped driver. CPU one/sixteen and CUDA responses and complete published states match independent oracles; the cross-user-write mutation is rejected before request compilation or CUDA.

## Fairness and limitations

JayDB2 uses RAM state, PostgreSQL uses temporary tables (no table WAL), and SQLite uses `:memory:`. This is a volatile compute comparison, not durability or equivalent access-policy throughput. SQL has no equivalent proof admission/authentication cost; the PostgreSQL session uses the local cluster administrator. PostgreSQL PL/pgSQL is interpreted, and SQLite recursive CTE is not intended for heavy numerical simulation. No Python SQL UDF or host simulation is timed. Each engine stores the same two parameter rows. Timed calls read Alice’s row and write identical Alice result rows at every completed size; separate untimed controls exercise both users.

JayDB2 preparation is per program; execution still uses a fresh child. One service/cluster session per backend and three samples are a focused observation, not a broad scaling or confidence study. Both engines’ complete tables, including unchanged Bob parameters/results, are checked after each completed SQL sample; JayDB2’s administrator feed checks the complete users/tables state. The scalar oracle cross-checks both users; NumPy independently evaluates every path and step at all sweep sizes, including sizes not completed by SQL.

All heavy commands held `/tmp/jaydb2-experiments-heavy.lock`, with unlimited stack. The benchmark ran under `paper/bench/fixed-clock.sh`: CPU performance policy with turbo disabled while measuring; the trap restored the captured policy. [Post-benchmark readback](simulation-frequency-restoration.json) confirms governor `powersave`, EPP `balance_performance`, and `no_turbo=0`. CUDA corpus: 512 MiB. GPU clock is unfixed and the GPU drives the desktop. No general speedup, kernel-only latency, resource quota, or compiler/GPU correctness claim follows. Input limits bound depth and steps, not physical execution time.

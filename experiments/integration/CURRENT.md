# Current experimental integration

`experiment-integration` follows main and contains the accepted CPU experiments,
SQL/Drizzle frontend, reproducible database comparison and optional official
CUDA backend. `SOURCES.json` records the input revisions. The Bend controller
replacement and quota enforcement are excluded. GPU support remains outside
main.

The GPU merge retains mainline helper startup/cleanup, best-effort diagnostics,
seed-free durable recovery, read certificates and the extended prepared
contract. Initialization, recovery and authentication always compile for CPU.
CUDA workers retain prebuilt device artifacts and before/after integrity checks.
CUDA programs remain exclusive even when certified CPU read batching is enabled;
there is at most one device worker per service instance. CPU read batching keeps
its existing FIFO and total CPU budget rules.

The focused GPU composition test pipelines certified CUDA reads with
`--read-workers 2`, checks ordered results and non-batched timing records, then
reopens the durable database, rejects an old handle and prepares a fresh one.
The other GPU gates check actual device execution, CPU/GPU publication parity,
unavailable devices, sealed artifacts and injected driver failures.

Historical experiment reports and measurement digests remain tied to their
original sources. They are not relabeled as measurements of this combined tree.
Fresh selected validation passed on the frozen candidate
`ad799835e4d7182180b9f1641561ba5ca8403b85`. HEAD and every tracked input
remained unchanged throughout the run. The subsequent merge brings in main's
documentation/validation record and updates this report; runtime, proof and test
sources remain identical to the tested candidate.

- All four real GPU cases passed, including the new composed read/timing/reopen
  test, unwrapped CPU/GPU state parity, real fault injection, sealed artifacts
  and unavailable-device behavior without automatic fallback.
- `make verify-integration test test-sql-native` exited zero: both official proof
  modes and rejection controls; 23 admission/verifier, 10 native-runtime, 45 Rust
  host and 19 service cases; 20 SQL proof checks, 26 SQL native integration cases
  and 31 SQL boundary checks.
- Formatting, strict all-target Clippy and accessory checks also passed. Main's
  fresh smoke components, comparison suite and paper evidence checks passed
  separately. Main's release binary built successfully.

[Machine-readable results](evidence/current-validation.json) retain the exact
candidate, commands, source-stability check and raw-log digest. The byte-exact
local logs remain ignored under `build/branch-integration-validation/`.
This is selected fresh validation, not a new complete release invocation.
Unchanged optional-library/index/receipt application, filesystem-fault and demo
suites retain the existing mainline source-bound validation.

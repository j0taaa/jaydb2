# Experimental GPU programs

This note records fresh evidence for optional official Bend 2.0.39 CUDA
execution in JayDB2. It does not alter the thesis's existing evidence dataset.
The implementation ports archived `4ff823d` / integration `ad79983` to the
current controller and exact prepared byte snapshots. CPU remains the default.

What is proved is the checked Book's semantics, under the existing T1–T3
assumptions: the same certificate, termination, access/RLS, canonical-size and
publication obligations apply to CPU and GPU programs. Both official checkers
must accept before GPU C emission/compilation/prebuild. No GPU-specific axiom
is added. The checked Gate/worker/finisher path still determines proposals and
publication. No Bend compiler/runtime or emitted C is modified.

With CUDA enabled, T2 grows to include the official CUDA code path in the
emitted runtime, NVRTC, CUDA driver, managed memory and GPU hardware.
Differential tests are evidence, not proof of compiler/runtime or GPU
correctness. Artifact integrity and process plumbing remain trusted host
obligations. Private reports bind the exact checked C, executable and cubin;
prepared programs additionally seal exact source, proof, manifest and artifact
bytes. Any rebuild notice or artifact change discards the proposal.

Fresh validation and measurements are recorded below.

The benchmark uses the same runtime-input `HeavyClient.bend` on CPU one
worker, CPU sixteen workers with `--gpu off` (Bend's own bang/parallel-let CPU
execution), and CUDA with one host worker and a 512 MiB corpus. The balanced
tree has 2^depth leaves and depth × 4096 mixing rounds per leaf. It executes
one explicit bang after a provisional credential write/read. Runtime text
input determines depth; preparation is outside the execution timings.
Python/NumPy independently performs every U32 round on every leaf at both
sizes and sums modulo 2^32. No native result supplies the expected checksum.

Native-worker wall time includes child startup, binary input/output, checked
selection/analysis, device initialization/load, computation, proposal encoding
and process exit. Complete prepared request time additionally includes host
authentication, all exact byte/hash integrity checks, publication, administrator
state-feed emission and response decoding. The administrator feed confirms
complete published state including Bob's unchanged credential. These are
separate trials, not additive phases or kernel-only timings. One warmup is
excluded per size/backend; three measured samples are retained.

The fixed-clock wrapper sets performance/no_turbo=1 and restores the captured
settings through a trap. The benchmark and every heavy validation hold
`/tmp/jaydb2-experiments-heavy.lock`. Run with `make benchmark-gpu`; the raw
file is `paper/evidence/gpu-programs.json`.

Limitations: Linux/NVIDIA with concurrent managed memory; one device worker
per instance, no cross-instance GPU scheduling, no multi-GPU selection, no
persistent device workers, no automatic CPU fallback on requested bangs, no
timeout or resource quota. The corpus bounds requested managed memory, not
total driver/device use. The current checkout has serial FIFO execution and
no read-batch executor to combine with CUDA. Source proofs do not imply a
runtime cost bound. Same-UID file-use races and vendor-library/hardware
correctness remain outside artifact checks. Device architecture changes can
force re-preparation. Results on a desktop GPU are observations on this
machine and workload, with no general speedup, throughput or break-even claim.
The harness fixes CPU policy, not GPU clocks; the GPU also drives the desktop.

## Fresh validation

The log file names refer to the gitignored `build/gpu/validation/` directory
of the machine that ran them; only tails and SHA-256 values are
retained in [gpu-validation.json](gpu-validation.json). This first table was
run on implementation revision `2c5c2f3`; the post-review rerun is recorded in
the section "Post-review fixes and rerun" below.

All heavy commands held the common lock with unlimited stack. Full raw local
logs and retained SHA-256 values are indexed in [gpu-validation.json](gpu-validation.json).
The table uses the final attempt for each requested command.

| Command | Result | Seconds | Real output summary |
| --- | --- | ---: | --- |
| `make build` (`make-build.log`) | PASS | 0.021 | Release binary |
| `make verify-contract` (`make-verify-contract.log`) | PASS | 49.902 | Both official modes; active/original contract hashes |
| `make verify` (`make-verify-rerun.log`) | PASS | 656.476 | All positive roots; 400 fixtures / 800 exact-false rejections; RLS proof controls |
| `make test` (`make-test-rerun.log`) | PASS | 617.519 | 47 admission/verifier; 10 native; 38 Rust; 16 service; 253 RLS responses |
| `make test-rls` (`make-test-rls.log`) | PASS | 94.022 | 253 native responses; 12 admission denials; both proof modes |
| `make test-accessories-native` (`make-test-accessories-native.log`) | PASS | 564.425 | 26 SQL CRUD; 31 limits; 600 random steps (638 SQL + 175 Drizzle comparisons); 11 TS responses; 2 starter profiles; 1 durable workflow |
| `make test-persistence` (`make-test-persistence.log`) | PASS | 532.736 | 8 tests |
| `make test-idempotency-recovery` (`make-test-idempotency-recovery.log`) | PASS | 80.994 | 1 lost-response/retry recovery test |
| `make prepared` (`make-prepared.log`) | PASS | 71.899 | 2 tests |
| `make smoke` (`make-smoke-rerun.log`) | PASS | 12.857 | Client/SQL/accessory unit suites; 38 Rust; fmt and strict Clippy |
| `make test-demo-web` (`make-test-demo-web.log`) | PASS | 137.272 | 12 tests |
| `make test-admission` (`make-test-admission.log`) | PASS | 74.016 | 47 tests |
| `make test-gpu` (`make-test-gpu-final.log`) | PASS | 188.963 | 5 real GPU integration methods; source equality, complete state, proof/integrity/device negatives and real launches |
| `python3 -m pytest paper/test_evidence.py` (`paper-test-evidence-final.log`) | PASS | 15.296 | 30 tests |
| `make benchmark-gpu` (`make-benchmark-gpu-final.log`) | PASS | 127.804 | 3 modes × 2 sizes; 36 measured native/request trials, plus warmups; independent oracles and full state |

Initial attempts are retained, including the new proof fixture's collision
with Base's `Pair` name and the extra CPU compiler argument that broke an
existing staging-test assumption. Both were corrected and rerun. The first
runner also failed to forward its inherited lock descriptor to nested targets;
the corrected runner uses `pass_fds=(9,)`. These are implementation/harness
failures, not claimed baseline failures. No failed attempt is counted as a pass.
The added observer bookkeeping initially decoded JSON metadata as canonical
state bytes; that test-reader bug was fixed. It also stopped the first
benchmark before any accepted raw measurement file was written. The trap
restored and verified powersave / EPP balance_performance / no_turbo=0.
A lightweight actual-socket framing check passed after the fix. The system
Python initially lacked pytest; the final evidence gate uses isolated wheel
dependencies under `build/gpu/python`, supplied through PYTHONPATH.

The initial unwrapped/forwarding GPU integration suite passed 5 tests in
167.810 seconds; the final strengthened suite additionally checks runtime
rebuilds, changes after launch, and exact CPU/CUDA emitted-C equality. The
forwarding driver trace counts are preserved in the final GPU log. Successful
interposed CUDA calls forward to the installed real driver. Unwrapped runs and
`CUDA_VISIBLE_DEVICES=''` tests are separate. Reports record `hasBangs`; the
tests and benchmark (not the production host) require it to be true and
inspect nonzero `#define BANGS` in the official emitted C.

## Post-review fixes and rerun

An independent review (Claude Opus 5.5) found no soundness blocker and five
should-fix items, all addressed in `ca9bbf7`: the default CPU worker path again
has only its original pre-run artifact check (post-run rechecks are CUDA-only);
CUDA build failures are compile-phase errors with no redundant pure re-check;
a pre-existing cubin is refused; resolved `libcuda`/`libnvrtc` paths and hashes
are recorded (not pinned); device-requirement, trusted-base and evidence wording
were corrected. On `ca9bbf7`, under the heavy lock: `cargo fmt --check`,
`make build`, `verify-contract` (50 s), `verify` (683 s), `test` (553 s),
`test-rls` (94 s), `test-persistence` (542 s), `test-idempotency-recovery`
(81 s), `prepared` (72 s), `test-demo-web` (138 s), `test-admission` (74 s),
`test-gpu` (184 s), `benchmark-gpu` (140 s) and `pytest paper/test_evidence.py`
(30 passed) all passed. `test-accessories-native` and `smoke` first failed in
that worktree only because its npm dependencies were not installed
(`drizzle-orm` / `tsc` not found); after `npm ci` both passed under the heavy
lock on the same revision: `test-accessories-native` (557 s) and `smoke` (13 s,
including strict Clippy and fmt). Exit codes, durations, SHA-256 of every full log and the
post-benchmark CPU restoration check are in
[gpu-validation-rerun.json](gpu-validation-rerun.json); the earlier
[restoration record](gpu-frequency-restoration.json) belongs to the first run.

## GPU proof fixtures

`tests/proof/GpuPrograms.bend` defines a program whose terminal value uses a
real bang (`mix!(x)`). Its positive law `bang_value` shows both checkers reduce
the bang exactly as the ordinary call. The three rejected fixtures fail exactly
at `false` under `--check-only` and `--verdict`: `GpuFalseResult` asserts a
wrong value through the bang (the checker must reduce `mix!`);
`GpuFalseTermination` and `GpuUnauthorizedRead` state a false termination bound
and the real `R.SafetyPrefix` access obligation for the bang program reading
another user's cell. The latter two fail for reasons independent of the bang:
they are controls showing that a bang changes no obligation. The full
certificate of a real bang client (`experiments/gpu/ClientProof.bend`) is
exercised at service level by `make test-gpu`.

## Focused fixed-clock measurements

Measured code revision `ca9bbf785249707d3315ca6a2cd60cfaa7bd2605` (post-review; clean tree). Raw samples, complete states, artifact hashes (including the recorded `libcuda`/`libnvrtc` paths and SHA-256), frequency settings and toolchain metadata: [gpu-programs.json](gpu-programs.json).

Native-worker and complete-request columns are **separate trials** (different
processes and device initializations), not nested phases; this is why a CUDA
complete-request median can be below its native-worker median.

| Workload | Backend / CPU workers | Native worker median (range), ms | Complete request median (range), ms |
| --- | --- | ---: | ---: |
| Depth 2, 32,768 rounds | cpu-1 / 1 | 3.238 (3.208–4.378) | 5.779 (5.654–6.109) |
| Depth 16, 4,294,967,296 rounds | cpu-1 / 1 | 7181.015 (7180.967–7181.637) | 7203.371 (7190.814–7222.371) |
| Depth 2, 32,768 rounds | cpu-16 / 16 | 4.096 (3.848–4.528) | 6.798 (6.613–7.529) |
| Depth 16, 4,294,967,296 rounds | cpu-16 / 16 | 530.453 (529.508–599.220) | 568.448 (557.944–569.818) |
| Depth 2, 32,768 rounds | cuda / 1 | 263.571 (258.702–277.842) | 218.787 (213.694–221.357) |
| Depth 16, 4,294,967,296 rounds | cuda / 1 | 272.773 (269.050–275.674) | 226.995 (226.080–263.754) |

An earlier run of the same harness at revision `2c5c2f3` (before the review
fixes, which do not touch the measured worker computation) observed the same
ordering with lower CUDA fixed overhead: CUDA 176.742 / 214.895 ms native
worker (small / large), cpu-16 496.948 ms and cpu-1 7179.807 ms on the large
size. The runs differ by more than their within-run ranges (CUDA small
+87 ms; cpu-16 large +7%; cpu-16 preparation 8.1 s vs 10.5 s). The cause was
not isolated: other heavy jobs were queued on the shared machine between runs
(each run itself held the exclusive lock), GPU clocks are not fixed and the GPU
also drives the desktop. Treat all figures as observations, not stable
constants.

[Standalone timing figure](gpu-programs.svg). The successful benchmark restored
and verified powersave / EPP balance_performance / no_turbo=0 before releasing
the heavy lock; see the [first-run restoration record](gpu-frequency-restoration.json) and, for the rerun, [gpu-validation-rerun.json](gpu-validation-rerun.json).

Preparation, including both checkers, compilation and optional official cubin prebuild, was measured separately (one sample each): cpu-1 8126.341 ms, cpu-16 10531.017 ms, cuda 13547.955 ms.

Both workload checksums come from the independent Python/NumPy oracle: depth 2: 1,321,445,589, depth 16: 3,867,567,763. Small arithmetic also matches a plain Python scalar loop. Every native proposal and every complete published state matches the independent full-state specification. All three modes emitted the same exact C hash.

The forwarding real driver observed 5 successful launches and 2 synchronizations for the exact HeavyClient emitted C used in all benchmark modes (`7cc266d3277b193b2df978f2f5bf7de0b00b620fc1d63d77cd57e4132e797cc3`). The official C has nonzero BANGS. Benchmarks themselves are unwrapped.

These wall-clock samples include fresh process/device costs. They do not isolate kernel execution, prove CUDA correctness or establish a general speedup. Three samples per mode/size are a focused observation, not a broad scaling study.

## Files and commits

Changed or added files:

- `INSTALL.md`
- `Makefile`
- `README.md`
- `SPECIFICATION.md`
- `experiments/gpu/Client.bend`
- `experiments/gpu/ClientProof.bend`
- `experiments/gpu/HeavyClient.bend`
- `experiments/gpu/README.md`
- `paper/bench/gpu_chart.py`
- `paper/bench/gpu_programs.py`
- `paper/evidence/gpu-frequency-restoration.json`
- `paper/evidence/gpu-programs.json`
- `paper/evidence/gpu-programs.md`
- `paper/evidence/gpu-programs.svg`
- `paper/evidence/gpu-validation.json`
- `proof/README.md`
- `server/main.rs`
- `tests/proof/GpuPrograms.bend`
- `tests/proof/VERIFY.bend`
- `tests/proof/rejected/GpuFalseResult.bend`
- `tests/proof/rejected/GpuFalseTermination.bend`
- `tests/proof/rejected/GpuUnauthorizedRead.bend`
- `tests/proof/test_proofs.py`
- `tests/service/gpu_faults.c`
- `tests/service/test_gpu.py`
- `tools/service/SIMPLE_SERVICE.md`
- `tools/service/compile.mjs`
- `tools/service/gpu-check.sh`
- `tools/service/stage.mjs`

Implementation commits before this evidence commit:

- `6a71dc0` Add sealed opt-in official CUDA program execution
- `5146d3d` Exercise GPU proof rejection, real launches and rollback
- `223428c` Avoid the Base Pair name in GPU proof fixtures
- `9237e5c` Preserve default compiler arguments and retain launch evidence
- `3976ef8` Document GPU proof boundary and add fixed-clock comparison harness
- `ecd4c74` Cross-check benchmark arithmetic and exact emitted C across backends
- `46eb6c9` Refresh default CPU and archived GPU branch descriptions
- `12bc8c6` Add reproducible GPU timing figure from retained raw samples
- `e22542a` Attest real HeavyClient device launches before timing runs
- `b31dd37` Check complete unchanged state with no visible CUDA device
- `2c5c2f3` Decode inspector metadata as JSON in GPU evidence reader

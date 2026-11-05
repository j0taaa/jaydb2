# Baseline experiment report

Base: `5925c57febd978d44fa24000233647a59e7898a6`.
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Measured driver: `e472fd41b2f4da0cac6eb607a501726fbe90f885`.
No prerequisite feature code is merged. Production files remain identical to
the common anchor. The separate preprocessing comparison measured
`26f8c9b739193eeb44c80b61129c38085e4be377`; its differences from accepted
`0f09c55dfff52fe10cd86b18a72a3241c5a92ad5` are an admission test and its report,
with no production change.

## Supported behavior and commands

The external CPU driver measures ordinary tiny reads/writes, repeated read
preparation, prepared reads/writes, eight-row transactions, different state
sizes and dependent computation. It checks every response, reads back every
changed row independently, and checks rollback after seven provisional valid
writes followed by an invalid eighth write. Computation takes both iteration
count and seed from runtime arguments and checks its exact U32 recurrence
against independent Python computation, including wraparound and zero steps.

```sh
./experiments/baseline/run.sh --smoke
./experiments/baseline/run.sh
/path/to/experiment-baseline/experiments/baseline/run.sh --root /path/to/experiment-X --smoke
/path/to/experiment-baseline/experiments/baseline/run.sh --root /path/to/experiment-X --executable target/release/jaydb2 --smoke
```

Both shell entrypoints automatically hold
`flock /tmp/jaydb2-experiments-heavy.lock`; do not wrap them in the same lock
again. Build, temporary worker files, generated sources and results stay local
to the selected worktree. The default uses three samples after one warmup,
8/64/256 rows and 250,000 compute steps; smoke uses two samples, no warmup,
8/64 rows and 4,096 steps. Rows carry 128 bytes of padding. Each size starts a
fresh checked eight-row seed, populates additional rows through an admitted
prepared `DefineRow` program, and reads every row before sampling. All three
canonical limits remain 32,768/65,536/32,768 bytes.

The selected controller is built with `cargo build --locked --release` into
`build/benchmark-target`. With `--executable`, the chosen binary must have the
same SHA-256 as this freshly built output; a mismatch refuses the run. Results
record the build command, selected root/revision and per-file source identity,
which must remain stable during the build. Do not edit either selected root
or the driver during a run. The exact driver snapshot, Git patches and
synthetic seed/proof sources are retained with local results. See
[README.md](README.md) for flags and the alternating-order comparison command.

## Contracts and proof scope

No production protocol, host, compiler, checker, runtime or proof changes.
The dedicated fixture explicitly installs zero administrator laws using the
existing `Free.configuration`. It measures that permissive policy while
retaining real admission, authentication and technical validation.

Generated `B.certificate` applies
`Free.execution_trace_free_covers_prefixes_and_final` to the exact submitted
program, actual context/arguments and configuration. `B.terminates` applies
`Termination.program_finite` with depth 2 for read/write/population, 9 for
batch and 1 for computation. The read finite-return helper covers every return
constructor. The real primary checker and BendTT admitted these certificates
through the normal service. Seed validity is checked normally. There is no new
formal functional theorem for the workload or Python harness; runtime output
assertions supply that evidence. Original compiler/native bridge assumptions
remain. No production deadlines, profiling framework, worker reuse or new
host protocol are introduced.

A preliminary expanded 64-row seed proof exceeded pinned BendTT fuel. This
was fixed by constructing larger states through admitted writes from the
checked small seed, without changing fuel or substituting a final-state check
for admission. An earlier parser diagnostic was fixed with a named finite
return helper. The failed diagnostic runs remain local at
`build/benchmark-first/result.json` and `build/benchmark-smoke/result.json`;
they are not passing baseline evidence.

## Actual validation and evidence

All performance/admission/native runs below used the heavy lock in the shell
entrypoint. The passing runs used the same committed driver and no tracked
patch. Only this report was untracked during measurement.

- `python3 -B -m unittest discover -s experiments/baseline -p 'test_*.py' -v`:
  **7 tests pass**. Covers statistics, warmup/failed-sample exclusion, CLI/size
  bounds, known recurrence answers, deliberately incorrect wire output,
  output-directory escape, stale executable refusal and changing-source refusal.
- `sh -n experiments/baseline/run.sh experiments/baseline/compare.sh`: pass.
- `./experiments/baseline/run.sh --smoke --output build/benchmark-smoke-populated`:
  **246 response checks pass**, 28 measured requests, 8/64 rows, about 106 seconds.
- `./experiments/baseline/run.sh --smoke --rows 256 --compute-iterations 250000 --output build/benchmark-default-boundary`:
  **564 response checks pass**, 14 measured requests, about 70 seconds.
  Includes 248 real population writes and readback of all 256 rows. Runtime
  computations `[250000,11300]` and `[250001,11301]` returned checked outputs
  `195281908` and `4265702928`.
- `./experiments/baseline/compare.sh --anchor-root /home/jota/.t3/worktrees/jaydb2/experiment-baseline --anchor-executable build/benchmark-target/release/jaydb2 --candidate-root /home/jota/.t3/worktrees/jaydb2/experiment-preprocessing --candidate-executable target/release/jaydb2 --samples 7 --warmups 2 --name benchmark-interleaved-accepted`:
  **22 response checks pass**, including 14 measured requests after two warmup
  rounds; alternating AB/BA order. Both chosen executables matched fresh builds.
- `git diff --check`: pass. Full contract/proof/regression suites were not
  repeated because production code is unchanged; the actual benchmark programs
  were checked and executed by the real service.

Total: **832 checked real responses**, including ordinary compilation,
preparation/reuse, successful publication, missing-row refusal, invalid writes,
partial-batch rollback, authentication failure, invalidation and zero compute.

Small committed machine-readable records retain all measured/warmup requests,
expected/actual outputs, full timing summaries, revisions, toolchain/hardware/
worker settings and source identities. Nonmeasured checks are grouped by
phase/workload/status. Each retained record identifies and hashes its complete
local result, which includes every setup/validation request and per-file build
source hashes:

- [Smoke](evidence/smoke.json): full record at
  `/home/jota/.t3/worktrees/jaydb2/experiment-baseline/build/benchmark-smoke-populated/result.json`.
- [Largest-state/default-compute boundary](evidence/boundary.json):
  `/home/jota/.t3/worktrees/jaydb2/experiment-baseline/build/benchmark-default-boundary/result.json`.
- [Interleaved anchor](evidence/interleaved-anchor.json):
  `/home/jota/.t3/worktrees/jaydb2/experiment-baseline/build/benchmark-interleaved-accepted-anchor/result.json`.
- [Interleaved preprocessing](evidence/interleaved-preprocessing.json):
  `/home/jota/.t3/worktrees/jaydb2/experiment-preprocessing/build/benchmark-interleaved-accepted-candidate/result.json`.

## Observations and limits

Measured on Linux x86-64, Intel i7-11700K, 16 logical CPUs, affinity 0..15,
about 16 GB RAM; one worker per native program, official C backend, GPU off.
Pinned Bend **2.0.39** source/binary and BendTT hashes were verified. Node
24.19.0, Python 3.12.3, Rust/Cargo 1.98.0, clang-19 19.1.1 with the existing
`-O2` flags. Full versions, exact hashes and load observations are in JSON.

Illustrative medians in milliseconds, **two samples per cell**:

| Rows | Model state bytes | Ordinary read | Read preparation | Prepared read |
| ---: | ---: | ---: | ---: | ---: |
| 8 | 1,865 | 3,895.035 | 3,980.137 | 8.036 |
| 64 | 13,401 | 3,876.450 | 3,996.637 | 17.628 |
| 256 | 52,953 | 3,901.844 | 3,990.454 | 30.335 |

Preparation/ordinary compilation dominates these small requests. The 256-row
prepared batch and 250,000-step compute medians were 35.244 and 33.089 ms;
these are complete requests, including current-state authentication, worker
creation, artifact checks, serialization and delivery. Population, validation
reads, startup and client expected-output calculation are outside the measured
request series. Warmups evolve the same deterministic model as samples.

The [interleaved chart](evidence/latency.html) shows all seven measured tiny
prepared reads per build: anchor median **16.769 ms**, MAD **5.224 ms**, range
8.037..25.747 ms; preprocessing median **10.557 ms**, MAD **3.337 ms**, range
7.104..19.528 ms. CV is about 0.40/0.42. This is a small noisy observation,
not a statistically established or general speedup. Exact controller hashes
are retained separately for both sides. The standard driver records stay in
their own worktrees; no feature report was edited here.

Only serial Linux CPU latency is supported here. No GPU, networking,
throughput, durability, scheduler/concurrency or restricted-policy costs.
Ordinary batch/compute admission is not timed; only read preparation has a
repeated preparation series. The full default three-sample/one-warmup command
was not run as an additional repetition; smoke and the minimal boundary run
exercise every workload, all advertised default sizes and the default compute
length. The runner currently expects the Cargo-based CLI/build interface.

External timing includes pipe delivery, not just service time. OS caches,
CPU frequency and unrelated load are uncontrolled. State hashes describe the
independent deterministic model; reads verify cells rather than exporting the
private state. Existing-executable verification requires reproducible output
with the current build recipe; use the default build if another legitimate
recipe produces different bytes. Cargo's cache, compiler and protected local
inputs remain trusted. No benchmark result establishes formal correctness or
hardware behavior beyond the stated checked observations.

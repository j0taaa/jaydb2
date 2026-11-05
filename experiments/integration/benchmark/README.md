# Fixed-budget CPU read comparison

Run from this worktree after the production sources are frozen:

```sh
experiments/integration/benchmark/run.sh --output build/integration/concurrency-benchmark
```

The runner takes the common heavy-work lock once. It builds this checkout's
Rust controller into `build/integration-benchmark-target`, records source and
binary hashes, and refuses changes during the build or measurement. Optional
`--executable target/release/jaydb2` also requires equality with that fresh
build. Output must be a new directory within this worktree. The default is one
warmup and seven alternating paired sample bursts, eight requests per burst,
and runtime iteration counts 0, 250,000 and 1,000,000. Override with
`--samples`, `--burst` or `--iterations` when documenting a follow-up run.

A separate proof check, without compiling or measuring the controller, is:

```sh
experiments/integration/benchmark/run.sh --check-only --output build/integration/benchmark-proof
```

Both official checkers check the fixture's universal administrator certificate,
finite termination proof, whole-continuation read-only witness and initial
validity. Actual runs still prepare through opcode 3 and the normal admission
and artifact-integrity path. The dedicated example uses the ordinary permissive
`Free` law set; technical validation and fresh authentication remain enabled.
This measures the host path rather than proof-checking costs for a restrictive
application. Preparation times are recorded separately.

`ReadCompute.bend` reads the current user's credential and returns it together
with a U32 recurrence checksum. Both recurrence count and seed come from actual
request arguments. The 0-iteration case measures a tiny real read. Larger cases
perform dependent serial arithmetic, permitting independent requests to use
different cores. Every response is compared with the credential and independent
Python arithmetic oracle; requests within each burst use different inputs. The
oracle uses logarithmic affine composition modulo 2^32 so larger runtime
counts do not spend billions of iterations in Python. `test_bench.py` compares
it with the baseline's independent direct-loop oracle across varied seeds,
small/large counts and U32 boundaries. Run these lightweight checks with
`python3 -B -m unittest discover -s experiments/integration/benchmark -v`.

The comparison holds `--threads 2` fixed and uses `--read-workers 1` versus `2`.
Both service process trees inherit affinity to the same two distinct physical
cores. The client, oracle and RSS sampler use other physical cores where
available, excluding SMT siblings of the selected service cores. No other
benchmark should run concurrently. This is a two-core CPU budget, not a claim
that individual native programs fully use every assigned worker.

Each burst is sent together in one pipe write and responses are read in FIFO
order. Burst throughput and per-request end-to-end p50/p95 latency include
queueing, authentication, artifact checks, native process startup/execution,
cleanup and delivery. There is no timing-log output, persistence or artificial
scheduler gate. Natural underfilling of an initial batch counts in the result.
The state has two users and no application tables; larger-state memory costs
are outside this comparison.

RSS is sampled every 10 ms for the selected controller and all descendants,
with task-child traversal so children started from read-worker threads count.
Also record RSS before each burst and after all responses have drained. Summed
RSS double-counts shared pages; sampling may miss short peaks. It is an
approximate observed process-tree footprint, not a total memory bound or PSS.
An idle second controller is outside the selected tree in both configurations.
Raw per-burst records, source/binary/toolchain identities, CPU topology,
preparation costs and summaries are retained in `result.json` and
`requests.jsonl`. No measured result is committed by this tooling itself.

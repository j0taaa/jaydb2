Run from this checkout:

```sh
./experiments/baseline/run.sh --smoke
./experiments/baseline/run.sh
```

`run.sh` holds `flock /tmp/jaydb2-experiments-heavy.lock` throughout build,
startup, admission and measurements. Do not wrap it in another `flock` on the
same lock. Use the existing pinned `.tools`; if absent, the authorized setup is
`ln -s /home/jota/projects/jaydb2/.tools .tools`. Nothing installs into or changes
that toolchain. Python's standard library, Rust/Cargo, Node and clang-19 are
required by the existing service. No production files are modified.

To measure another existing worktree with the **same benchmark fixture**:

```sh
/path/to/experiment-baseline/experiments/baseline/run.sh \
  --root /path/to/experiment-X --smoke
```

The runner normally builds that checkout using `cargo build --locked --release`
and a target-local `build/benchmark-target`. An existing executable can be
chosen explicitly (its source provenance is the caller's responsibility):

```sh
/path/to/experiment-baseline/experiments/baseline/run.sh \
  --root /path/to/experiment-X --executable target/release/jaydb2 --smoke
```

Every run creates a new target-local `build/bench-UTC-pid/` directory; override
with `--output build/NAME` (must be new and inside `--root`). It contains
`result.json`, request journals and stderr per state size, deterministic seed
and proof sources, a snapshot of the driver, and tracked Git patches. All
subprocess temporary files are inside its `tmp/`; no shared mutable build,
cache or state directory is used. A failed check makes the command nonzero and
writes `status: failed`; never compare the partial timings as passing results.

The default has three measured samples after one warmup for each transaction,
8/64/256 application rows with 128 bytes of padding per row, one native CPU
worker, and 250,000 dependent U32 recurrence iterations per compute request.
The smoke profile has two samples, no warmup, 8/64 rows and 4,096 iterations.
Overrides: `--samples N` (at least 2), `--warmups N`, `--rows 8 64 256` (each
8..256), `--threads N` (1..128), `--compute-iterations N`. Increasing samples
adds costly ordinary admission/compilation; keep comparisons modest.

Each state size starts a fresh process and deterministic seed. The first
invalid-credential response records startup separately. The workloads are:

- `read`: one cell in the **last** row, ordinary and prepared.
- `write`: replace that cell with a new runtime integer, ordinary and prepared;
  an independent prepared read verifies each published write.
- `batch`: eight writes in one prepared transaction, each independently read
  afterward. A one-row state is intentionally excluded.
- `compute`: prepared execution of the serial recurrence
  `x = (1664525*x + 1013904223) mod 2^32`. Iteration count and seed arrive via
  the actual call arguments and change each sample; Python independently
  computes the checked expected result. Zero iterations are also checked.

Repeated **read preparation** records real universal certificate checking and
native compilation, invalidating each previous handle. Other workload
preparations are setup records, deliberately excluded from timing summaries.
Prepared executions still run fresh native workers and normal authentication,
artifact validation and publication. Ordinary read/write submissions send the
full code and concrete proof every time. Batch/compute ordinary admission is
not measured. Warmups mutate the same deterministic model as measured writes;
all changed rows are read back. Missing rows, schema-invalid writes with
rollback, invalid credentials, invalidation and zero computation are checked.

The dedicated schema explicitly installs **zero administrator laws** using the
existing `Free.configuration`; every request still passes real admission,
termination checking and all three canonical technical limits. This measures
the permissive benchmark policy, not the cost of a restricted application.
The termination proof witnesses actual finite actions (2 steps for tiny
read/write, 9 for batch, 1 for pure compute). It does not assert functional
correctness of the recurrence; checked runtime outputs provide that evidence.

Timings use a monotonic clock immediately before writing an already encoded
request through receiving the complete response bytes. Client encoding,
decoding, expected-output calculation and validation reads are outside each
sample. Pipe delivery, host scheduling/authentication, admission where
applicable, fresh native execution/cleanup and response delivery are included.
This is external latency, not a new production service-time metric. No
production deadline or profiling framework is added. No GPU, durability,
network, concurrency or throughput claim is made.

`result.json` records individual samples, medians, min/max, median absolute
deviation, sample standard deviation and coefficient of variation, together
with exact target/driver revisions and dirty-patch hashes, driver hashes,
controller hash, verified pinned compiler/checker hashes, tool versions,
CPU/OS/memory/affinity/load and explicit worker/backend settings. Full exact
request bytes are represented by SHA-256, with source/proof snapshots and
arguments retained. Random instance handles and absolute paths vary between
runs. The state sizes/hashes describe the deterministic **model**; independent
reads verify touched cells rather than claiming the host exported its private
state. Repetitions share an instance and OS caches; they are not independent
cold boots. Locking coordinates these experiments, not unrelated machine load.

Lightweight runner tests (no proof/native work):

```sh
python3 -B -m unittest discover -s experiments/baseline -p 'test_*.py' -v
```

For a small comparison after both chosen executables exist:

```sh
/path/to/experiment-baseline/experiments/baseline/compare.sh \
  --anchor-root /path/to/experiment-baseline \
  --anchor-executable build/benchmark-target/release/jaydb2 \
  --candidate-root /path/to/experiment-preprocessing \
  --candidate-executable target/release/jaydb2
```

This holds the same heavy lock, starts two independent eight-row instances,
prepares the same read once in each, then alternates AB/BA request order for
two warmup rounds and seven measured rounds. It does not build or modify
feature code. Results remain in each target's own
`build/interleaved-UTC-{anchor,candidate}/result.json`. Setup is excluded;
there is one global in-flight request and both instances remain alive during
sampling. It measures tiny prepared latency only. Inspect each controller hash
and revision and the retained samples before drawing any conclusion. This
small comparison is sensitive to cache effects, system load and sample count.

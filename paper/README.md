# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, and an editable
Portuguese Beamer defense presentation. Build with `make -C paper`; output is
under `.build/tcc/output/`. The paper and slides are being updated separately
from the evidence pipeline. LaTeX needs pdfLaTeX, AMS, Times, geometry,
microtype, natbib, booktabs, hyperref, Beamer and PGF.

## Reproducing the fresh evidence

Each benchmark JSON records its exact source commit and executable/source
fingerprints. The harness uses the real serial Rust host, official Bend 2.0.39 and
BendTT, literal emitted C, Clang 19, and one native worker thread. No mock
engine, alternate verifier, concurrent read batches, or historical executable
is measured. All output values are checked. Initialization and warmups are
outside the operation samples. JSON files include raw nanoseconds, outputs,
CPU/kernel/toolchain/commit metadata and executable/source fingerprints.
JayDB2 round trips start with sending a pre-encoded frame and end after the
complete framed response is read; decoding/checking are outside that interval.
SQL intervals surround `execute(...).fetchall()` and include driver
encoding/decoding. Result checks are outside every operation interval.

Install the pinned JayDB2 toolchain following `INSTALL.md`. This checkout used
an ignored `.tools` symlink to the already installed pinned tools. Build first:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
```

PostgreSQL is installed without root. On Ubuntu 24.04, the following downloads
and extracts binaries into this worktree only. Existing system libraries meet
the other binary dependencies on the measured machine; inspect `ldd` if needed.
`uv` installs the Python driver into an ignored directory (Python 3.12):

```sh
mkdir -p .build/paper-bench/pg-packages
(cd .build/paper-bench/pg-packages && apt-get download postgresql-16=16.15-0ubuntu0.24.04.1 postgresql-client-16=16.15-0ubuntu0.24.04.1 libpq5=16.15-0ubuntu0.24.04.1)
for p in .build/paper-bench/pg-packages/*.deb; do dpkg -x "$p" .build/paper-bench/pg; done
uv pip install --python /usr/bin/python3 --target .build/paper-bench/python 'psycopg[binary]==3.3.8'
```

Run each experiment under the common lock. The harness does not acquire a
nested lock. PostgreSQL uses a private cluster and local Unix socket, starts
and stops with the comparison, and never uses a system service. Reruns replace
only benchmark artifacts under `.build/paper-bench/` and the five primary JSON outputs (the initial failed seed attempt is retained
separately):

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/run.py latency'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/run.py prepared'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/run.py comparison'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/run.py scaling'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/run.py verification'
python3 -B paper/evidence.py
python3 -B -m unittest discover -s paper -p test_evidence.py -v
```

`ordinary.json` has ten measured calls per program after one warmup.
`prepared.json` has three registrations and 300 measured executions per
program/storage mode. The indexed transaction alternates the Boolean value.
Voucher calls issue fresh equal-length IDs and retire each voucher with a
checked, separately timed maintenance call to bound state size. Registration
samples include real certificate checking and optimized compilation; these
three samples have no discarded registration warmup. Every session first
waits for initialization via an untimed rejected-credential request.

`comparison.json` has 300 measured reads and updates per engine/policy, plus
ten measured durable ordinary JayDB2 calls per operation for context. Writes
change the integer. JayDB2 writes return an acknowledgment and each is checked
by a separate untimed readback; SQL writes return their stored value. JayDB2
uses existing access-law proof combinators with owner-named tables. PostgreSQL
uses an owner column, a non-superuser/non-BYPASSRLS role, enabled and forced
RLS, and synchronous commits. Cross-user reads/updates must fail admission in
JayDB2 and affect/return no rows in PostgreSQL. The PostgreSQL `rls` settings in the JSON describe the ownership arm; the
point arm has RLS disabled. SQLite is explicitly an
**unconstrained baseline**, with WAL and `synchronous=FULL`. The point workload
has ten rows; the ownership workload has ten rows for each of two users.

`scaling.json` retains the 65,536-byte application state ceiling, measures 50
reads and 50 updates per supported population/mode. It starts from an empty
valid seed and populates it through a universally certified prepared transaction
that returns the checked row count; that handle is invalidated before sampling.
It records larger populations or failed attempts explicitly. Rows have a seven-byte ID and one
int64 cell. An independently admitted full-row writer probes the first excess
row after the point-operation samples. Scaling latency includes transfer, decoding,
validation, lookup and publication; it does not isolate copying alone. Both
operations target the lexicographically last key, so linear lookup also grows
with population.
`verification.json` retains complete command outputs and wall times, inventories and source-size definitions.
The retained `scaling-seed-attempt.json` records the initial direct-seed
approach: the unmodified BendTT checker exhausted fuel in `Seed.initial_valid`
at 1,000 and 1,105 rows. These are initialization/checker failures, not measured
operation latencies. The final scaling procedure avoids that large seed proof. An initial boundary
probe also had an affine-key error in benchmark source; the corrected probe
reuses the admitted population program. Its two rejected attempts are retained
in `corrected_harness_failures`; the two maximum-size groups were re-measured,
and the six smaller groups were retained. `supplemental_run` records that
measurement run's metadata.

To reproduce the initial failed 1,000-row seed check after setting up the harness
(the command is expected to exit nonzero with `Seed.initial_valid: out of fuel`):

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B -c "from paper.bench.run import BUILD, Session; from paper.bench.fixtures import package; Session(package(BUILD / \"seed-fuel-repro\", \"read\", rows=1000), \"seed-fuel-repro\").close()"'
```

Counts of `law` declarations, proof definitions and named theorem witnesses
are distinct syntactic facts; they are not equivalent proof-strength metrics.

All spreads are inclusive quartiles (Q1 and Q3); medians and quartiles are
derived from raw samples without outlier removal. The preparation break-even
is `ceil(median_registration / (median_ordinary - median_prepared))`, using
matching volatile programs, excluding service startup. This is an amortization
model over the measured medians, not a guarantee for every state or call. E1
voucher samples accumulate ten issued vouchers; E2 bounds state with retirements.
Closed-loop throughput includes validation gaps
and the voucher maintenance calls. Active-call throughput is the median rate over ten consecutive blocks of 30
calls, computed as 30 divided by the sum of their measured round trips. It
excludes maintenance and gaps; its table reports quartiles across ten blocks.
The full closed-loop rate is one 300-call batch observation. These two rates
have deliberately different boundaries.

Set `JAYDB_BENCH_TIMING=1` only for the opt-in diagnostic phase hooks. The
ordinary and prepared experiments enable it; comparison and scaling do not.
Phase records include staging, bootstrap/preflight, parse/audit, primary check,
binding audit/seal, official BendTT translation/check, C emission, C compilation,
worker execution, cleanup and publication. `admission_total` contains the Node
subphases and must not be added to them. The oracle-soundness law's share is
included in whole-Book checking: the pinned APIs expose no per-law timer.
Timing hooks never change protocol bytes or admission decisions. The existing
service timer also writes raw sidecars under the ignored build directory.

## Evidence macros

`python3 -B paper/evidence.py` writes `.build/tcc/numbers.tex`, booktabs table
fragments (`ordinary-table`, `prepared-table`, `phase-table`,
`database-comparison-table`, `registration-phase-table`, `throughput-table`, `verification-table`, `size-table`, `scaling-table`),
`scaling-coordinates.tex`, and four `scaling-{volatile,persistent}_{read,update}.dat`
files with `rows median_ms` columns for pgfplots. Include `numbers.tex` once.
No macro name contains digits. Quartiles and sample counts are in table
fragments; no measurement is copied manually into the manuscript.

| Macro names | Meaning | Unit |
|---|---|---|
| `\OrdinarySamples`, `\PreparedSamples`, `\RegistrationSamples`, `\ComparisonSamples`, `\ScalingSamples` | Measured sample count per program, mode, or operation | samples |
| `\OrdinaryReadMedianSeconds`, `\OrdinaryIndexedMedianSeconds`, `\OrdinaryVoucherMedianSeconds` | Ordinary median latency by program (Read, Indexed, Voucher) | Seconds |
| `\PreparedReadVolatileMedianMs`, `\PreparedIndexedVolatileMedianMs`, `\PreparedVoucherVolatileMedianMs`, `\PreparedReadPersistentMedianMs`, `\PreparedIndexedPersistentMedianMs`, `\PreparedVoucherPersistentMedianMs` | Prepared median latency by program and storage mode | Ms |
| `\RegistrationReadVolatileMedianSeconds`, `\RegistrationIndexedVolatileMedianSeconds`, `\RegistrationVoucherVolatileMedianSeconds`, `\RegistrationReadPersistentMedianSeconds`, `\RegistrationIndexedPersistentMedianSeconds`, `\RegistrationVoucherPersistentMedianSeconds` | One-time registration median by program and storage mode | Seconds |
| `\PreparedReadVolatileCallsPerSecond`, `\PreparedIndexedVolatileCallsPerSecond`, `\PreparedVoucherVolatileCallsPerSecond`, `\PreparedReadPersistentCallsPerSecond`, `\PreparedIndexedPersistentCallsPerSecond`, `\PreparedVoucherPersistentCallsPerSecond` | Observed full-loop throughput, one 300-call batch (includes voucher retirements) | calls/s |
| `\PreparedReadVolatileActiveCallsPerSecond`, `\PreparedIndexedVolatileActiveCallsPerSecond`, `\PreparedVoucherVolatileActiveCallsPerSecond`, `\PreparedReadPersistentActiveCallsPerSecond`, `\PreparedIndexedPersistentActiveCallsPerSecond`, `\PreparedVoucherPersistentActiveCallsPerSecond` | Median active throughput, ten consecutive 30-call blocks (maintenance/gaps excluded) | calls/s |
| `\BreakEvenReadCalls`, `\BreakEvenIndexedCalls`, `\BreakEvenVoucherCalls` | Volatile preparation break-even by program, from measured median costs | calls |
| `\OrdinaryMedianSeconds`, `\PreparedMedianMs`, `\BreakEvenCalls` | Default point-read aliases: ordinary seconds, volatile prepared milliseconds, volatile break-even calls | s / ms / calls |
| `\PostgresPointReadMedianMs`, `\PostgresPointUpdateMedianMs`, `\SqlitePointReadMedianMs`, `\SqlitePointUpdateMedianMs`, `\JayPointReadMedianMs`, `\JayPointUpdateMedianMs`, `\PostgresOwnerReadMedianMs`, `\PostgresOwnerUpdateMedianMs`, `\SqliteOwnerReadMedianMs`, `\SqliteOwnerUpdateMedianMs`, `\JayOwnerReadMedianMs`, `\JayOwnerUpdateMedianMs` | Durable comparison medians: engine, Point/Owner policy, Read/Update operation | Ms |
| `\OrdinaryJayPointReadMedianSeconds`, `\OrdinaryJayPointUpdateMedianSeconds`, `\OrdinaryJayOwnerReadMedianSeconds`, `\OrdinaryJayOwnerUpdateMedianSeconds` | Durable ordinary JayDB2 median: Point/Owner policy, Read/Update operation | Seconds |
| `\VerifyContractSeconds`, `\VerifySeconds`, `\TestSeconds` | Wall time of the named make target, one run | s |
| `\VerifyContractExitCode`, `\VerifyExitCode`, `\TestExitCode` | Required verification command exit status (zero means passed) | exit code |
| `\NegativeFixtures` | negative fixtures | count |
| `\ContractTheoremTypes` | theorem types | count |
| `\ProofLawDeclarations` | proof law declarations | count |
| `\ProofDefinitions` | proof definitions | count |
| `\ProofTheoremWitnesses` | Named top-level theorem witnesses (names ending theorem); excludes supporting lemmas | witnesses |
| `\SrcNonblankLines`, `\ContractNonblankLines`, `\ProofNonblankLines`, `\ServerNonblankLines`, `\ToolsNonblankLines`, `\NativeNonblankLines` | Nonblank source lines including comments; Src, Contract, Proof, Server, Tools (admission + service), Native | lines |
| `\ContractCoverageModules`, `\SrcCoverageModules`, `\ProofCoverageModules`, `\LibraryCoverageModules` | Modules reached by the maintained verification import roots, by directory | modules |
| `\StateLimitBytes` | Configured canonical state ceiling | bytes |
| `\StateMaximumRows` | Largest analytically fitting population of this row shape | rows |
| `\LargeSeedFuelFailures` | Retained large direct-seed initialization attempts exhausted official BendTT fuel | attempts |

The article should continue to distinguish the executable theorems from the
T1–T3 integration premises and finite tests. These measurements establish
neither unconditional executable correctness nor a performance advantage over
PostgreSQL or SQLite. The removed read-batch experiment and historical
comparison evidence are no longer inputs to this pipeline.

## Investigating latency variability

The CPU's `powersave` policy can alternate between approximately 4.6 GHz and
800 MHz during these short serial operations. Use the separate diagnostic to
record native body wall time, process CPU time, endpoint CPU frequencies, page
faults and context switches alongside the existing phase timings:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/diagnose.py'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; strace -f -tt -T -s 100 -o .build/paper-bench/diagnostic.strace -e trace=read,write,execve,wait4,futex,poll,ppoll,pselect6,clock_nanosleep,mmap,munmap,madvise,fsync,rename,close python3 -B paper/bench/diagnose.py --calls 5 --output .build/paper-bench/diagnostic-traced.json'
```

The diagnostic compiles `paper/bench/worker-clock.c` as an opt-in `LD_PRELOAD`
observer. It does not alter the emitted C, native executable, wire bytes or
execution decision. It adds observation overhead and is **not** enabled in the
headline experiments. Endpoint frequency is a sampled policy observation, not
an integrated hardware cycle counter. `DIAG START/END` delimit sampled calls in
the syscall trace; initialization/registration and idle pipe waits are outside
that window. No governor, affinity or power setting is changed by the harness.
Persistent equal-state successes now reuse their durable image; changed state,
including new receipt rows, still follows file sync/rename/directory sync.

The performance follow-up is recorded in `paper/evidence/performance-report.txt`
and `performance-summary.json`, including before/after medians, inclusive
quartiles, sample counts, validation and fingerprints for all E1–E5 cases.
`latency-diagnosis.json` retains separate observer samples and syscall excerpts;
these diagnostic timings are not inputs to the headline tables.

# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, with a **Portuguese
defense presentation**: 20 main frames and six appendix frames (the executable
theorem list and the eleven T3 host duties). Both use LaTeX; the slides use Beamer, with
Portuguese speaker notes in each frame. Change wording and layout directly in `slides.tex`.

```sh
make -C paper
```

Requires Python 3 and pdfLaTeX with standard AMS, newtxtext/newtxmath, Latin Modern, caption, geometry, microtype,
natbib, booktabs, hyperref, Beamer, PGF and PGFPlots packages. Build products stay ignored
under `.build/tcc/`; the deliverables are:

- `.build/tcc/output/jaydb2-tcc.pdf`
- `.build/tcc/output/jaydb2-defense.pdf`

The article and slides describe the serial executable Bend gate, generated
admission-oracle proof, worker Commit/Keep decision, and checked prepared
controller and registry. The article develops the model, architecture,
executable guarantees and trusted base T1–T3, then the indexed ownership and
voucher/receipt applications. Its evaluation covers ordinary admission cost,
prepared reuse, durable and owner-only point operations against PostgreSQL 16
and SQLite, verification cost, and complete-state size scaling.

The build regenerates validated evidence before compiling both documents. The direct
outputs are `.build/tcc/main.pdf` and `.build/tcc/slides.pdf`; the Makefile copies
them to the delivery paths above. Every measured result comes from generated
macros, tables or plot data, so rerunning the evidence builder updates both documents.
The final evaluation uses the fixed-clock evidence described below; historical
frequency-scaling runs are retained only for diagnosis and provenance.

The organization roughly follows the author's
[tcc-final article](https://github.com/j0taaa/tcc-final/tree/main/paper), while
using a self-contained article layout and this project's executable specification.
The current [PUC Minas library guidance](https://www.pucminas.br/biblioteca/DocumentoBiblioteca/ABNT-GUIA-COMPLETO-Elaborar-formatar-trabalho-cientifico.pdf)
and the [2026 ICEI article example](https://www.overleaf.com/latex/templates/modelo-de-artigo-icei-puc-minas/bxwcdrxpdgbc)
informed the format. The specific course's submission template, advisor,
committee, defense date and any mandatory translated abstract still need local
confirmation before submission; they have not been invented. The main text
and abstract are English as requested. Source bibliography titles retain their
original language.

## Reproducing the fresh evidence

Each benchmark JSON records its exact source commit and executable/source
fingerprints. The harness uses the real serial Rust host, official Bend 2.0.39 and
BendTT, literal emitted C, Clang 19, and one native worker thread. The final protocol uses independent sessions at the nominal base clock with
the performance governor and turbo disabled. E5 uses one session with
log-spaced populations and a first-key variant. Historical frequency-scaling
measurements are excluded from the final latency evaluation. No mock engine or alternate verifier
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

The final E1–E3 and E5 evidence uses the i7-11700K at its nominal 3.6 GHz
base clock. `paper/bench/fixed-clock.sh COMMAND ...` saves every CPU's governor
and EPP and Intel `no_turbo` before changing anything. It applies `performance`,
`performance`, and `no_turbo=1`, verifies the settings, runs the command, and
restores and verifies the exact saved values on EXIT, INT, TERM or HUP. The
wrapper retains original/applied/restored JSON under `.build/paper-bench/frequency-*`;
the final restoration receipt is written to `paper/evidence/cpu-restoration.json`
by `check-clock.py`, which also exercises nonzero exit, INT, TERM and HUP.
Original values are `powersave`, `balance_performance`, and `no_turbo=0` on
all 16 logical CPUs. The recovery JSON can be restored manually with
`sudo -n python3 -B paper/bench/frequency.py restore PATH/TO/original.json`.
As with any shell trap, SIGKILL or machine power loss cannot run cleanup; the
saved recovery file is written before changing the policy.

Every new result's metadata and each session/size record contain the policy,
all 16 sampled `scaling_cur_freq` values (kHz), inherited CPU affinity and UTC.
Samples near 3.6 GHz support the configured policy; they are endpoint
observations, not integrated hardware cycle measurements. No `taskset` pinning
is applied: the harness, all engines and their children inherit the same CPU
set. Scaling records `session_count=1`; E1–E3 use three sessions per condition.

Run the commands under the common heavy-work lock, with unlimited stack and
`make build` first. The wrapper does not acquire a nested lock. PostgreSQL
uses a new private cluster and local Unix socket for **every engine/condition/
session**, starts and stops with the harness, and never uses a system service.
SQLite gets a fresh connection/database; JayDB2 gets a fresh service and durable
database for each E1–E3 session. The full final reproduction is:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build && paper/bench/fixed-clock.sh bash -c "python3 -B paper/bench/run.py latency && python3 -B paper/bench/run.py prepared && python3 -B paper/bench/run.py comparison && python3 -B paper/bench/run.py scaling"'
# E4 wall times are retained from the previous unchanged implementation;
# optionally replace them with a new controlled run:
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build && paper/bench/fixed-clock.sh python3 -B paper/bench/run.py verification'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build && paper/bench/fixed-clock.sh python3 -B -m paper.bench.source_sizes --update'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build && python3 -B paper/bench/check-clock.py'
python3 -B paper/evidence.py
python3 -B -m unittest discover -s paper -p test_evidence.py -v
```

`ordinary.json` measures ten calls per program in each of three independent
sessions (30 pooled), after one excluded warmup per session. Program order
rotates by session. E1 voucher issues accumulate ten vouchers; the indexed set
alternates false/true. `prepared.json` measures three registrations and 300
calls per program/storage/session: nine registrations and 900 calls pooled.
Registration has no discarded warmup and reports **min/median/max**, not
quartiles of three observations. Each session invalidates its first two handles
before registering its measured handle, so one entry remains live. Voucher
executions issue equal-length fresh IDs and then retire them with a separately
checked maintenance call. Each session waits for initialization with an
untimed rejected-credential request. Prepared condition order rotates by two
positions per session, changing the program and storage order.

`comparison.json` measures 300 reads and 300 changing integer updates per
engine/policy/state/session (900 pooled per operation). Small-state ordinary
JayDB2 context has ten samples per operation/session (30 pooled), after one
warmup. SQL/JayDB2 timing boundaries are described above; JayDB2 updates return
an acknowledgement with a separate untimed checked readback; SQL returns the
integer. Engine order and state/policy condition order rotate by session.
The two **total** row counts are 10 and 1,104 in every engine, in both policy
arms. The owner arm splits rows equally between Alice and Bob (5+5 or
552+552); this corrects the previous owner arm's 10+10 versus point arm's 10.
The operation targets the last Alice key. The large owner state uses 65,500
canonical bytes of the unmodified 65,536-byte ceiling; the point arm uses
65,444 bytes. A certified universally quantified population program initializes
these states from an empty valid seed; the owner population reuses the access
example's ownership and termination inductions and runs separately as each user.
The benchmark ownership law also permits `DefineRow` and `CountRows` only on
the authenticated user's table, for certified initialization. Its timed
`ReadCell`/`DefineColumn` ownership and column restrictions are unchanged.
Population and initialization are outside measured samples.

Cross-user checks run for **both states in every session**, and JSON retains
exact SQL or full JayDB2 program/proof/arguments, credentials and outcomes:

- JayDB2: Alice submits an **ordinary** program whose read or update operation
  names Bob's table, with the unchanged ownership certificate. Admission returns
  `certificate` and no value for both attempts. Bob then uses the legitimate
  universal prepared program to verify his row is still zero. This measures
  rejection of the supplied certificate, not a theorem that arbitrary invalid
  programs can never obtain certificates.
- PostgreSQL 16.15: the non-superuser, non-BYPASSRLS `bench_alice` role issues
  `SELECT value FROM cells WHERE owner='bench_bob' AND id='k000000'` and
  `UPDATE cells SET value=999 WHERE owner='bench_bob' AND id='k000000' RETURNING value`.
  ENABLE/FORCE RLS and `owner=current_user` return/affect zero rows; the
  administrator verifies Bob's value remains zero. The point arm disables RLS.
- SQLite: the same SQL **succeeds** on the unconstrained connection, returning
  Bob's zero and then 999. The harness resets Bob's value afterward. SQLite is
  an unconstrained baseline with WAL and `synchronous=FULL`, not an ownership
  mechanism. PostgreSQL uses fsync, synchronous commits and full-page writes.

`scaling.json` is **one experimental session**, with one service process per
storage mode reused across every ascending size: 10, 30, 100, 300, 600,
1,000 and the maximum 1,105 rows (65,503 bytes). This makes within-mode size
comparisons share the same process and registered point program. A certified
population transaction resets all rows to zero at each size; its handle is
invalidated before timing. Each point has 50 reads and 50 changing updates,
after one warmup per operation. Target is the last key; first-key reads add 50
observations at 10 and 1,105 rows in both storage modes. First- and last-key
reads run on the same all-zero state before timed updates. Complete-state transfer,
decoding, validation, linear lookup and publication remain included; comparing
first and last key helps distinguish lookup from complete-state work without
claiming to isolate either. The first excess row is actually attempted and
must return `limit`; an absent-row read confirms rollback. Canonical sizes for
1,106 and 10,000 rows are retained as untimed failures. The historical
`scaling-seed-attempt.json` records direct-seed BendTT fuel failures and is
retained for provenance, not pooled with final operation samples.

`verification.json` retains its successful original `make verify-contract`,
`make verify`, and `make test` wall times and full output; these are single runs
under the earlier powersave/turbo policy, **not fixed-clock comparisons**.
The new `detailed_sizes` inventory separates the Rust host's nonblank physical
lines (comments/imports/attributes included) in `server/*.rs`: each
`#[cfg(test)]` attribute and its following top-level item through the unindented
closing brace count as test lines; all remaining lines count as production.
The file-level split sums exactly to the existing host total. Feature-gated
fault injection remains production under this syntactic definition unless
inside a `cfg(test)` item.

Client program lines count `applications/indexed/Client.bend` for Indexed and
`applications/vouchers/Client.bend` **plus `Voucher.bend`** for Voucher (the
six-line wrapper delegates the actual dispatcher there). Client proof lines
count Indexed's `ClientProof.bend`, `CheckedActions.bend`, `Completion.bend`,
and Voucher's `ClientProof.bend`. Ratios are proof/program nonblank lines.
These local client-certificate counts exclude reusable library/kernel proofs,
model/schema/seed files, shared application ownership proofs, and the separate
voucher functional theorem suite; they are scoped client integration costs,
not complete application correctness-proof sizes. `detailed_sizes` lists every
included file and its count. Counts of `law` declarations, proof definitions
and named theorem witnesses remain distinct syntactic facts.

Statistics use inclusive quartiles, without outlier removal. Tables report
pooled median [Q1,Q3] and a separate min–max of the three session medians in
`session-spread-table.tex` (JayDB2 latency conditions) and `paper/evidence/final-headlines.md` (E5 has one
session, so its session range is degenerate). E2 registration instead uses
min/median/max over nine observations. Preparation break-even remains
`ceil(median_registration / (median_ordinary - median_prepared))`, matching
volatile programs and excluding startup; it is an amortization model over
medians. Active throughput uses 30 consecutive blocks of 30 measured calls
(ten per session), excludes maintenance/gaps, and reports pooled quartiles.
Closed-loop throughput records three independent 300-call batch rates,
including validation gaps and voucher retirements; its macro is their median.
No pooling crosses a session boundary when forming throughput blocks.

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
`database-comparison-table`, `registration-phase-table`, `registration-table`,
`session-spread-table`, `throughput-table`, `verification-table`, `size-table`, `scaling-table`),
`ordinary-phase-summary.tex`, named coordinate macros in `scaling-coordinates.tex`,
the versioned `final-summary.json`, `final-headlines.md` and `final-report.md`
under `paper/evidence/`, and four `scaling-{volatile,persistent}_{read,update}.dat` files with
`rows state_bytes median_ms lower_ms upper_ms` columns for pgfplots. The last two
columns are distances from the median to Q1 and Q3; coordinate macros use decimal
kB on the horizontal axis and ms on the vertical axis. Include `numbers.tex` once.
No macro name contains digits. Integers use `{,}` grouping for English article text and math. `numbers.tex` detects the Beamer class and supplies raw integer tokens there, preserving the slides' existing PGF number helpers. Use grouped integer macros directly in English prose/math; numeric PGF parsers should receive raw numeric values; latency table columns use two decimals, or three for E3 and session medians to retain SQL read resolution, in one unit per latency table. Quartiles appear in table fragments and sample counts in macros/captions; no measurement is copied manually into the manuscript.

| Macro names | Meaning | Unit |
|---|---|---|
| `\OrdinarySamples`, `\PreparedSamples`, `\RegistrationSamples`, `\ComparisonSamples`, `\ScalingSamples` | Pooled measured sample count per program, mode, or operation (30/900/9/900/50) | samples |
| `\OrdinaryReadMedianSeconds`, `\OrdinaryIndexedMedianSeconds`, `\OrdinaryVoucherMedianSeconds` | Ordinary median latency by program (Read, Indexed, Voucher) | s |
| `\PreparedReadVolatileMedianMs`, `\PreparedIndexedVolatileMedianMs`, `\PreparedVoucherVolatileMedianMs`, `\PreparedReadPersistentMedianMs`, `\PreparedIndexedPersistentMedianMs`, `\PreparedVoucherPersistentMedianMs` | Prepared median latency by program and storage mode | ms |
| `\RegistrationReadVolatileMedianSeconds`, `\RegistrationIndexedVolatileMedianSeconds`, `\RegistrationVoucherVolatileMedianSeconds`, `\RegistrationReadPersistentMedianSeconds`, `\RegistrationIndexedPersistentMedianSeconds`, `\RegistrationVoucherPersistentMedianSeconds` | One-time registration median by program and storage mode | s |
| `\PreparedReadVolatileCallsPerSecond`, `\PreparedIndexedVolatileCallsPerSecond`, `\PreparedVoucherVolatileCallsPerSecond`, `\PreparedReadPersistentCallsPerSecond`, `\PreparedIndexedPersistentCallsPerSecond`, `\PreparedVoucherPersistentCallsPerSecond` | Median full-loop throughput across three independent 300-call batches (includes voucher retirements) | calls/s |
| `\PreparedReadVolatileActiveCallsPerSecond`, `\PreparedIndexedVolatileActiveCallsPerSecond`, `\PreparedVoucherVolatileActiveCallsPerSecond`, `\PreparedReadPersistentActiveCallsPerSecond`, `\PreparedIndexedPersistentActiveCallsPerSecond`, `\PreparedVoucherPersistentActiveCallsPerSecond` | Median active throughput, thirty 30-call blocks (ten per session) (maintenance/gaps excluded) | calls/s |
| `\BreakEvenReadCalls`, `\BreakEvenIndexedCalls`, `\BreakEvenVoucherCalls` | Volatile preparation break-even by program, from measured median costs | calls |
| `\OrdinaryMedianSeconds`, `\PreparedMedianMs`, `\BreakEvenCalls` | Default point-read aliases: ordinary seconds, volatile prepared milliseconds, volatile break-even calls | s / ms / calls |
| `\PostgresPointReadMedianMs`, `\PostgresPointUpdateMedianMs`, `\SqlitePointReadMedianMs`, `\SqlitePointUpdateMedianMs`, `\JayPointReadMedianMs`, `\JayPointUpdateMedianMs`, `\PostgresOwnerReadMedianMs`, `\PostgresOwnerUpdateMedianMs`, `\SqliteOwnerReadMedianMs`, `\SqliteOwnerUpdateMedianMs`, `\JayOwnerReadMedianMs`, `\JayOwnerUpdateMedianMs` | Durable comparison medians: engine, Point/Owner policy, Read/Update operation | ms |
| `\OrdinaryJayPointReadMedianSeconds`, `\OrdinaryJayPointUpdateMedianSeconds`, `\OrdinaryJayOwnerReadMedianSeconds`, `\OrdinaryJayOwnerUpdateMedianSeconds` | Durable ordinary JayDB2 median: Point/Owner policy, Read/Update operation | s |
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
| `\OrdinaryReadCheckingSeconds`, `\OrdinaryIndexedCheckingSeconds`, `\OrdinaryVoucherCheckingSeconds` | Median of the per-call sum of primary and BendTT whole-Book checking | s |
| `\OrdinaryReadCompilationSeconds`, `\OrdinaryIndexedCompilationSeconds`, `\OrdinaryVoucherCompilationSeconds` | Median of the per-call sum of C emission and compilation | s |
| `\OrdinaryReadWorkerMs`, `\OrdinaryIndexedWorkerMs`, `\OrdinaryVoucherWorkerMs` | Median worker phase wall time | ms |
| `\OrdinaryReadOtherSeconds`, `\OrdinaryIndexedOtherSeconds`, `\OrdinaryVoucherOtherSeconds` | Median per-call round trip minus checking, C generation/build and worker; includes all remaining work/communication | s |
| `\OrdinaryReadWorkerSharePercent`, `\OrdinaryIndexedWorkerSharePercent`, `\OrdinaryVoucherWorkerSharePercent` | Median of per-call worker/round-trip shares | % |
| `\JayPointReadOverPostgres`, `\JayPointReadOverSqlite`, `\JayPointUpdateOverPostgres`, `\JayPointUpdateOverSqlite`, `\JayOwnerReadOverPostgres`, `\JayOwnerReadOverSqlite`, `\JayOwnerUpdateOverPostgres`, `\JayOwnerUpdateOverSqlite` | Ratio of durable prepared JayDB2 median to the named SQL median, with matching policy and operation | ratio |
| `\ProofToImplementationRatio` | Nonblank `proof/` lines divided by `src/` lines, including comments | ratio |
| `\ScalingSmallRows`, `\ScalingMiddleRows`, `\ScalingLargeRows` | Legacy scaling anchors: 10, 100 and 1,000 rows | rows |
| `\StateMaximumBytes`, `\StateFirstExcessRows`, `\StateFirstExcessBytes` | Canonical bytes at the maximum fitting population, first excess row count, and bytes at first excess | bytes / rows / bytes |
| `\StateOversizedRows`, `\StateOversizedBytes`, `\StateOversizedKilobytes` | Largest requested out-of-configuration population and its canonical size; not timed | rows / bytes / decimal kB |
| `\ScalingSmallVolatileReadMedianMs`, `\ScalingSmallVolatileUpdateMedianMs`, `\ScalingSmallPersistentReadMedianMs`, `\ScalingSmallPersistentUpdateMedianMs`, `\ScalingMaximumVolatileReadMedianMs`, `\ScalingMaximumVolatileUpdateMedianMs`, `\ScalingMaximumPersistentReadMedianMs`, `\ScalingMaximumPersistentUpdateMedianMs` | Prepared median at the smallest and maximum fitting scaling populations, by storage/operation | ms |
| `\CpuGovernor` | Governor and EPP for all 16 CPUs (`performance`) | text |
| `\CpuClockGHz` | Nominal base clock (sampled endpoints retained separately) | GHz |
| `\TurboSetting` | Intel turbo state (`disabled`, `no_turbo=1`) | text |
| `\SessionCount` | Independent sessions per E1–E3 condition; E5 uses one | sessions |
| `\RustProductionLines`, `\RustTestLines` | Rust host nonblank production/test physical lines, split by cfg(test) items | lines |
| `\IndexedClientLines`, `\IndexedProofLines` | Indexed client program and local certificate/helper nonblank lines, files defined above | lines |
| `\IndexedProofRatio` | Indexed proof/program line ratio | ratio |
| `\VoucherClientLines`, `\VoucherProofLines` | Voucher client wrapper+dispatcher and local certificate nonblank lines, files defined above | lines |
| `\VoucherProofRatio` | Voucher proof/program line ratio | ratio |
| `\ComparisonLargeRows` | Total rows per engine in the large comparison (both policy arms) | rows |
| `\LargeJayReadMs`, `\LargeJayWriteMs`, `\LargePgReadMs`, `\LargePgWriteMs`, `\LargeSqReadMs`, `\LargeSqWriteMs` | Large-state durable point read/update median: JayDB2, PostgreSQL, SQLite | ms |
| `\LargeOwnerJayReadMs`, `\LargeOwnerJayWriteMs`, `\LargeOwnerPgReadMs`, `\LargeOwnerPgWriteMs`, `\LargeOwnerSqReadMs`, `\LargeOwnerSqWriteMs` | Large-state durable owner-arm read/update median: JayDB2, PostgreSQL FORCE RLS, unconstrained SQLite | ms |
| `\ScalingFirstKeySmallMs`, `\ScalingFirstKeyLargeMs` | Volatile first-key read median at smallest and maximum population | ms |

The integration also derives these macros from the same samples:

| Macro names | Meaning | Unit |
|---|---|---|
| `\OrdinarySessionSamples`, `\RegistrationSessionSamples` | Calls or preparations per E1/E2 session | samples |
| `\PreparedBatchCalls` | Prepared calls per independent full-loop batch | calls |
| `\ThroughputBlocks`, `\ThroughputBlockCalls` | Pooled active-throughput blocks and calls per block | blocks / calls |
| `\ScalingSessionCount` | Independent E5 sessions | sessions |
| `\PreparedIndexedPersistentSessionMinMs`, `\PreparedIndexedPersistentSessionMaxMs` | Min/max of durable indexed session medians, including the slow session | ms |
| `\ScalingVolatileReadSlopeUsPerRow` | Least-squares slope of volatile last-key read medians against row count | microseconds/row |

The article's session table selects E1/E2 latencies and JayDB2 E3 latencies;
the retained final report includes every engine, throughput and E5 range.
The fitted slope summarizes only the measured row shape and populations.

The article and slides distinguish the executable theorems from the
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
that window. The diagnostic alone does not change policy; run it inside `fixed-clock.sh` to compare under the final policy.
Durable equal-state successes reuse their durable image; changed state,
including new receipt rows, still follows file sync/rename/directory sync.

The historical performance follow-up is recorded in `paper/evidence/performance-report.txt`
and `performance-summary.json`, including before/after medians, inclusive
quartiles, sample counts, validation and fingerprints for all E1–E5 cases.
`latency-diagnosis.json` retains separate observer samples and syscall excerpts;
these diagnostic timings are not inputs to the headline tables.

Preparation means one-time checking and compilation; registry means the
prepared handle registry. Generated filenames and macro names retain their
original registration/persistent spelling.

## Claim and reference review

A successful unchanged-state Commit updates the RAM root/response pair while
reusing the durable image. Changed states complete full-image write, file
fsync, atomic replacement and directory fsync before publication and reply;
open synchronizes the validated authoritative file and directory once.
Recovery checks configuration and identity, not a proof of recovered-root
validity. Recovered-root validity assumes an image produced by this host's own
commits, a T1 persistence obligation outside the eleven in-memory T3 duties; the voucher
lost-response/restart scenario is tested, not proved. The article and speaker
notes state this boundary explicitly. Execution is serial and schema/laws are
fixed; logical termination is not a wall-clock bound.

References were checked against author copies, publisher proceedings and
Crossref's publisher-deposited DOI metadata. The bibliography retains natbib
author–year citations with an alphabetized ABNT-style reference list. Specific
verification sources are:

- Sheard and Stemple, TODS (1989), pages 322–368:
  [publisher DOI](https://doi.org/10.1145/68012.68014), verified against its
  Crossref record and the author's institutional publication listing.
- Chlipala, UrFlow, OSDI (2010), pages 105–118:
  [author page](https://adam.chlipala.net/papers/UrFlowOSDI10/) and
  [MIT record](https://dspace.mit.edu/entities/publication/f21a3560-bda9-4731-b3ee-4c916aedb509).
  No DOI is asserted for this USENIX paper.
- Giffin, Levy, Stefan, Terei, Mazières, Mitchell and Russo, Hails, OSDI (2012),
  pages 47–60: [USENIX record and BibTeX](https://www.usenix.org/conference/osdi12/technical-sessions/presentation/giffin).
  No DOI is asserted for this USENIX paper.
- Parker, Vazou and Hicks, LWeb, PACMPL 3 (POPL), article 75 (2019), 30 pages:
  [author record](https://www.cs.umd.edu/~mwh/papers/parker19lweb.html),
  author PDF and [publisher DOI](https://doi.org/10.1145/3290388).
- Yang, Hance, Austin, Solar-Lezama, Flanagan and Chong, Jacqueline, PLDI (2016),
  pages 631–647: [author PDF](https://www.cs.cmu.edu/~jyang2/papers/p631-yang.pdf)
  and [proceedings DOI](https://doi.org/10.1145/2908080.2908098).
- Chen, Ziegler, Chajed, Chlipala, Kaashoek and Zeldovich, FSCQ, SOSP (2015),
  pages 18–37: [author page](https://adam.chlipala.net/papers/FscqSOSP15/),
  SIGOPS proceedings and [publisher DOI](https://doi.org/10.1145/2815400.2815402).
- Necula, PCC, POPL (1997), pages 106–119:
  [author bibliography](https://people.eecs.berkeley.edu/~necula/papers.html)
  and [publisher DOI](https://doi.org/10.1145/263699.263712), alongside the
  existing Necula–Lee technical report.
- Ynot's ICFP (2008) entry now uses the
  [proceedings DOI](https://doi.org/10.1145/1411204.1411237), whose Crossref
  container is ICFP, rather than the SIGPLAN Notices DOI. Fiat's POPL (2015)
  entry adds pages 689–700 and the
  [proceedings DOI](https://doi.org/10.1145/2676726.2677006), verified against
  the [author PDF](https://adam.chlipala.net/papers/FiatPOPL15/FiatPOPL15.pdf)
  and Crossref metadata.
- PostgreSQL 16: [CREATE TABLE / deferrability](https://www.postgresql.org/docs/16/sql-createtable.html),
  [constraint triggers](https://www.postgresql.org/docs/16/sql-createtrigger.html),
  [unsupported assertions](https://www.postgresql.org/docs/16/unsupported-features-sql-standard.html)
  and [row-security filtering](https://www.postgresql.org/docs/16/ddl-rowsecurity.html).

Table privileges or a reference monitor can prevent forbidden reads before
they occur. The benchmark uses shared-table RLS filtering; per-owner table
privileges would be a closer analogue to the application layout. Proofs here
combine arbitrary propositions, all-path admission without policy aborts and
amortized preparation; they are not justified by claiming runtime checks occur
only after observation. The source listing copies the indexed entry
and `Policy.Rule` branches, omitting imports and helper definitions. Bend is
used so that one checked Book contains both the proofs and the functions
compiled to C; this choice does not assert superiority over other proof assistants.
The oracle generator is untrusted because its output is checked, while checker
soundness and source binding remain trusted. Agreement between the related
checker modes is not independent evidence of logical soundness.

## Final examiner derivations and review

The scaling figures use a linear row axis. The intercept and slope come from
one least-squares fit of volatile last-key read medians against row count;
the intercept estimates fixed per-call cost within this measured range, not
an independently isolated phase. Volatile updates nearly coincide with reads.
The state ceiling limits both the execution evidence and demonstrated checking
scale; direct large-seed failures are retained, not treated as timed operations.

The inventory adds maintained Bend files from `library/` and
`applications/vouchers/proof/` by recursively counting nonblank physical lines,
including imports and comments. It does not change the evidence JSON. The
`proof/src` ratio excludes both areas. The local voucher certificate imports
`Receipts` and `ReceiptLaws` from the library, so its local ratio benefits from
reusable proofs. Twelve witness names end in `_theorem`; three codec/framing
witnesses have other names (the four Core clauses share one witness).

The execution and architecture frames remain separate: one explains private
state and the publication decision; the other explains processes and source
binding. Positioning now immediately follows the research questions. The
conclusion answers RQ1–RQ3 before future work. The deck retains 20 main frames
and six appendix frames.

New macros derived for this review (all emitted into `numbers.tex`):

| Macro | Meaning / unit |
|---|---|
| `\RegistrationReadVolatileCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationReadVolatileCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationIndexedVolatileCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationIndexedVolatileCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationVoucherVolatileCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationVoucherVolatileCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationReadPersistentCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationReadPersistentCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationIndexedPersistentCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationIndexedPersistentCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationVoucherPersistentCheckingSeconds` | Preparation whole-Book checking median (s) |
| `\RegistrationVoucherPersistentCompilationSeconds` | Preparation C emission/build median at -O2 (s) |
| `\RegistrationCheckingMinSeconds` | Range of preparation phase medians across programs/storage modes (s) |
| `\RegistrationCheckingMaxSeconds` | Range of preparation phase medians across programs/storage modes (s) |
| `\RegistrationCompilationMinSeconds` | Range of preparation phase medians across programs/storage modes (s) |
| `\RegistrationCompilationMaxSeconds` | Range of preparation phase medians across programs/storage modes (s) |
| `\ComparisonOwnerRowsPerUser` | Rows per user in the even large ownership split (rows) |
| `\LargeJayReadOverPostgres` | Large-state durable point JayDB2 / Postgres median (ratio) |
| `\LargeJayReadOverSqlite` | Large-state durable point JayDB2 / Sqlite median (ratio) |
| `\LargeJayUpdateOverPostgres` | Large-state durable point JayDB2 / Postgres median (ratio) |
| `\LargeJayUpdateOverSqlite` | Large-state durable point JayDB2 / Sqlite median (ratio) |
| `\LargeOwnerJayUpdateQthreeMs` | Large owner update pooled upper quartile (ms) |
| `\LargeOwnerJayUpdateSessionMinMs` | Large owner update session-median spread (ms) |
| `\LargeOwnerJayUpdateSessionMaxMs` | Large owner update session-median spread (ms) |
| `\PublicTheoremWitnesses` | Named top-level witnesses plus the separately named codec/framing witnesses (witnesses) |
| `\LibraryFiles` | Library maintained Bend files (files) |
| `\LibraryNonblankLines` | Library nonblank Bend lines, including comments (lines) |
| `\VoucherSuiteFiles` | Voucher proof suite maintained Bend files (files) |
| `\VoucherSuiteNonblankLines` | Voucher proof suite nonblank Bend lines, including comments (lines) |
| `\ScalingVolatileReadInterceptMs` | Intercept of the same least-squares volatile last-key read fit (ms) |

Additional reference checks on 11 November 2026:

- Schneider, *Enforceable security policies*, TISSEC 3(1), 30–50 (2000):
  [author PDF](https://www.cs.cornell.edu/fbs/publications/EnfSecPols.pdf)
  verifies execution monitoring before a violating step, and
  [Crossref publisher metadata](https://api.crossref.org/works/10.1145/353323.353382)
  verifies author, title, venue, issue, pages, date and DOI
  [10.1145/353323.353382](https://doi.org/10.1145/353323.353382).
- PostgreSQL 16 [privileges](https://www.postgresql.org/docs/16/ddl-priv.html):
  verified the roles of SELECT, GRANT and REVOKE, including inherited and
  PUBLIC privileges. This documentation entry is now in the bibliography.
- Bend attribution: the official [organization](https://github.com/bendlang)
  identifies itself as BendLang; its [repository](https://github.com/bendlang/bend)
  credits Victor Taelin and the team. The corporate-author entry is BendLang,
  rather than attributing the current distribution to a different organization.
  The unrelated proof-assistant name list was removed; Malecha et al.'s cited
  database work still identifies its Coq/Ynot implementation.

The article uses natbib author–year citations and a consistently alphabetized
ABNT-style bibliography. Existing bibliography entries are retained.

## Examiner completion checklist

| Request | Status and resolution |
|---|---|
| C1 | Done: abstract and §4.2 distinguish each native worker from the separate checked native control executable; §4.2 and prepared-program notes identify `ControlBridge.packet` → `Control.control`. |
| C2 | Done: table privileges and reference monitors prevent reads before they occur; GRANT/REVOKE and deferred triggers are acknowledged. The three-part proof rationale, PostgreSQL comparison threat, early positioning frame and Portuguese note agree. Schneider DOI verified before inclusion. |
| M1 | Done: both figures use linear 0–1,200 row axes. Updates are drawn first, reads remain visible, near-coincidence is disclosed, and a same-fit intercept macro accompanies closely linear growth. |
| M2 | Done: article and limitations frame disclose the configured byte/row ceiling, failed large seeds and untested checking/execution scale beyond it; full explanation is in the Portuguese note. |
| M3 | Done: maintained library and voucher proof suite added to inventory using source-derived nonblank-line/file macros with tests. Central proof/src and local voucher ratio exclusions and library imports are explicit. |
| M4 | Done: T1 states own-commit provenance for recovered roots as a persistence obligation outside eleven in-memory T3 duties; §4.3, §8 and notes agree. |
| M5(a) | Done: generated preparation-phase table follows the preparation-distribution table; measured checking/compilation ranges use derived macros. |
| M5(b) | Done: durable variability includes the large owner update's Q3, median and session spread; no unmeasured per-fsync attribution is made. |
| M6 | Done: positioning follows research questions; final frame answers RQ1/RQ2/RQ3; readable footnotesize code shows all Rule branches and an unscaled small table; ordinary totals added. Optional merge considered and not taken: execution and architecture explain distinct boundaries, so both diagrams remain. |
| M7 | Done: rewritten abstract explains the conditional executable guarantee, vacuity repair and applications in plain language, gives ordinary/prepared and SQL headline costs, locates the separate controller and avoids claiming isolated state/storage costs. |
| Numbers: trailing zeros | Done: fixed zerofill in article and Portuguese latency/number helpers. |
| Numbers: ratios | Done: comparison and proof ratios use zero or one decimal. |
| Fonts: article | Done: newtxtext/newtxmath replace Times; matching math numerals; redundant amssymb removed to avoid duplicate symbol definitions. |
| Fonts: slides | Done: Latin Modern loads before Helvetica; pdffonts confirms no Type 3 fonts. |
| Captions | Done: caption package with 4pt skip. |
| Table 6 | Done: small, unscaled phase table in seconds; obsolete units sentence removed. |
| Table 2 | Done: tools and Rust counts explicitly say lines; official checkers marked external. |
| Figure 1 | Done: manual break after “both checkers,” prevents checker hyphenation. |
| Wording: E5 session | Done: “In a single…” rather than a generated numeral at sentence start. |
| Wording: negative cases | Done: sentence begins with “The”, not a numeral. |
| Wording: positive fixture | Done: task-list application and applications/tasks path introduced. |
| Wording: witness count | Done: `_theorem` names distinguished from codec/framing witnesses and from four clauses sharing Core; total witness macro is derived. |
| Wording: registry | Done: handle registry distinguished from user registry in §4.2 and theorem table. |
| Wording: image reuse | Done: full explanation kept in §4.3; one short reminder in E5. Redundant article explanations in E2, E3 and §8 removed. |
| Wording: conclusion | Done: RQ answers precede future work. |
| Wording: ordinary owner read | Done: higher measured cost reported; cause explicitly not isolated rather than guessed. |
| Sources: large population | Done: largest even near-ceiling owner split explained with per-user and total-row macros. |
| Sources: large SQL ratios | Done: read/update ratios derived and reported; conclusion includes large-state costs. |
| Sources: T3.2 | Done: “prepared opcode bytes”. |
| Sources: T3.10 | Done: authenticated empty-proof artifact-map miss for unknown/invalidated HANDLE, with live-artifact availability distinction; appendix agrees. |
| Sources: CPU | Done: active cores under performance policy distinguished from idle-core endpoint readings; no global fixed-governor/clock assertion. |
| Bibliography: retention | Done: existing entries retained. |
| Bibliography: Bend | Done: BendLang attribution checked against official organization and repository credits. |
| Bibliography: style | Done: natbib author–year with consistent ABNT-style list. |
| Bibliography: assistant names | Done: unsupported comparison name list removed; cited Malecha et al. still supports the Coq/Ynot database description. No unrelated new references needed. |
| Portuguese: permissions diagram | Done: diagram separated from title, unexplained line removed, índice kept unbroken, publication sentence made precise. |
| Portuguese: trusted base | Done: oracle-generator and Rust-test wording corrected; T3 size says linhas. |
| Portuguese: prepared call | Done: fresh authentication/current arguments/checked selection/private execution wording. |
| Portuguese: cost slide | Done: preparation pays after derived call count; “Execução no worker”; ordinary totals shown. |
| Portuguese: SQL comparison | Done: small read/update ratios shown as macros; large read ratio explicit; generic “orders/factor” summary removed. |
| Portuguese: limitations | Done: guarantee covers exactly installed laws under T1–T3. |
| Portuguese: conclusion | Done: preparation-compensation line uses macro and median-model qualifier. |
| Portuguese: T3 duty 7 | Done: latest unchanged registry bytes, exact T1 tuple and only checked delta. |
| Portuguese: vacuity | Done: redundant green positive-control line removed. |
| Portuguese: appendix layout | Done: 2mm inter-row spacing via booktabs addlinespace after complete wrapped rows; avoids baseline collisions. |
| Notes: title | Done: “e o custo do protótipo atual”. |
| Notes: handle freshness | Done: handle never previously allocated in the instance. |
| Notes: publication decision | Done: “à decisão Commit ou Keep”. |
| Research question 3 | Done: current certified executable cost and reduction through prepared reuse. |

Validation: `make -C paper` succeeds; final second-pass logs contain no undefined
references/macros or overfull boxes. All 25 evidence unit tests pass. Every
article page and defense slide was rendered with `pdftoppm -png -r 60` and
visually inspected; diagram hyphenation, wrapped-row spacing and two vertical
overflows found during inspection were fixed. Final artifacts contain 21 article
pages and 26 defense slides (20 main plus six appendix), with a Portuguese
speaker note in every frame. Evidence JSON, benchmarks and all source outside
the permitted paper files are unchanged. No push is performed.

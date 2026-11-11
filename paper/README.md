# TCC manuscript and defense slides

English article by **Gabriel Jota Lizardo, PUC Minas**, with a **Portuguese
defense presentation**: 20 main frames and six appendix frames (the executable
theorem list and the eleven T3 host duties). Both use LaTeX; the slides use Beamer, with
Portuguese speaker notes in each frame. Change wording and layout directly in `slides.tex`.

```sh
make -C paper
```

Requires Python 3 and pdfLaTeX with standard AMS, Times, geometry, microtype,
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
`pending-macros.tex` is loaded immediately after `numbers.tex` in both documents.
It supplies red, named fallbacks for the new measurement fields; generated
definitions take precedence through `\providecommand`. The preparation-spread
and session-spread tables use `\IfFileExists` and show a red pending-table marker
until their generated fragments arrive. Existing numbers remain the retained
evidence until the measurement work is integrated; the fixed-frequency protocol
and new comparisons need a final reconciliation against that evidence before
submission. Do not treat a successful PDF build as completion of that measurement pass.

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
BendTT, literal emitted C, Clang 19, and one native worker thread. The revised protocol uses independent sessions with a fixed CPU clock, the
performance governor and turbo disabled. E5 uses one session with log-spaced
populations and a first-key variant. The earlier run under frequency scaling
is discarded for the revised evaluation; its diagnosis remains in
`paper/evidence/performance-report.txt`. No mock engine or alternate verifier
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

`ordinary.json` supplies `\OrdinarySamples` calls per program after warmup.
`prepared.json` supplies `\RegistrationSamples` preparations and
`\PreparedSamples` measured executions per program/storage mode and session. The indexed transaction alternates the Boolean value.
Voucher calls issue fresh equal-length IDs and retire each voucher with a
checked, separately timed maintenance call to bound state size. Registration
samples include real certificate checking and optimized compilation; these
samples have no discarded preparation warmup. Every session first
waits for initialization via an untimed rejected-credential request.

`comparison.json` supplies `\ComparisonSamples` measured reads and updates
per engine/policy and session, plus `\OrdinarySamples` durable ordinary
JayDB2 calls per operation for context. Writes
change the integer. JayDB2 writes return an acknowledgment and each is checked
by a separate untimed readback; SQL writes return their stored value. JayDB2
uses existing access-law proof combinators with owner-named tables. PostgreSQL
uses an owner column, a non-superuser/non-BYPASSRLS role, enabled and forced
RLS, and synchronous commits. Cross-user reads/updates must fail admission in
JayDB2 and affect/return no rows in PostgreSQL. The PostgreSQL `rls` settings in the JSON describe the ownership arm; the
point arm has RLS disabled. SQLite is explicitly an
**unconstrained baseline**, with WAL and `synchronous=FULL`. The small point workload uses `\ScalingSmallRows`; the large point uses
`\ComparisonLargeRows` near the state limit. Ownership profiles use the stated
population for each of two users.

`scaling.json` retains the `\StateLimitBytes` state ceiling and supplies
`\ScalingSamples` reads and updates per supported population/mode. The revised
E5 uses log-spaced populations and a first-key read variant in one session. It starts from an empty
valid seed and populates it through a universally certified prepared transaction
that returns the checked row count; that handle is invalidated before sampling.
It records larger populations or failed attempts explicitly. Rows have a seven-byte ID and one
int64 cell. An independently admitted full-row writer probes the first excess
row after the point-operation samples. Scaling latency includes transfer, decoding,
validation, lookup and publication; it does not isolate copying alone. Both
operations target the lexicographically last key, so linear lookup also grows
with population. Unchanged-state reads reuse the already durable image;
state-changing durable calls add full-image write and synchronization.
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
voucher samples accumulate issued vouchers; E2 bounds state with retirements.
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
`ordinary-phase-summary.tex`, named coordinate macros in `scaling-coordinates.tex`,
and four `scaling-{volatile,persistent}_{read,update}.dat` files with
`rows state_bytes median_ms lower_ms upper_ms` columns for pgfplots. The last two
columns are distances from the median to Q1 and Q3; coordinate macros use decimal
kB on the horizontal axis and ms on the vertical axis. Include `numbers.tex` once.
No macro name contains digits. Quartiles appear in table fragments and sample counts in macros/captions; no measurement is copied manually into the manuscript.

| Macro names | Meaning | Unit |
|---|---|---|
| `\OrdinarySamples`, `\PreparedSamples`, `\RegistrationSamples`, `\ComparisonSamples`, `\ScalingSamples` | Measured sample count per program, mode, or operation | samples |
| `\OrdinaryReadMedianSeconds`, `\OrdinaryIndexedMedianSeconds`, `\OrdinaryVoucherMedianSeconds` | Ordinary median latency by program (Read, Indexed, Voucher) | s |
| `\PreparedReadVolatileMedianMs`, `\PreparedIndexedVolatileMedianMs`, `\PreparedVoucherVolatileMedianMs`, `\PreparedReadPersistentMedianMs`, `\PreparedIndexedPersistentMedianMs`, `\PreparedVoucherPersistentMedianMs` | Prepared median latency by program and storage mode | ms |
| `\RegistrationReadVolatileMedianSeconds`, `\RegistrationIndexedVolatileMedianSeconds`, `\RegistrationVoucherVolatileMedianSeconds`, `\RegistrationReadPersistentMedianSeconds`, `\RegistrationIndexedPersistentMedianSeconds`, `\RegistrationVoucherPersistentMedianSeconds` | One-time registration median by program and storage mode | s |
| `\PreparedReadVolatileCallsPerSecond`, `\PreparedIndexedVolatileCallsPerSecond`, `\PreparedVoucherVolatileCallsPerSecond`, `\PreparedReadPersistentCallsPerSecond`, `\PreparedIndexedPersistentCallsPerSecond`, `\PreparedVoucherPersistentCallsPerSecond` | Observed full-loop throughput, one 300-call batch (includes voucher retirements) | calls/s |
| `\PreparedReadVolatileActiveCallsPerSecond`, `\PreparedIndexedVolatileActiveCallsPerSecond`, `\PreparedVoucherVolatileActiveCallsPerSecond`, `\PreparedReadPersistentActiveCallsPerSecond`, `\PreparedIndexedPersistentActiveCallsPerSecond`, `\PreparedVoucherPersistentActiveCallsPerSecond` | Median active throughput, ten consecutive 30-call blocks (maintenance/gaps excluded) | calls/s |
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
| `\ScalingSmallRows`, `\ScalingMiddleRows`, `\ScalingLargeRows` | First three measured scaling populations, sorted by row count | rows |
| `\StateMaximumBytes`, `\StateFirstExcessRows`, `\StateFirstExcessBytes` | Canonical bytes at the maximum fitting population, first excess row count, and bytes at first excess | bytes / rows / bytes |
| `\StateOversizedRows`, `\StateOversizedBytes`, `\StateOversizedKilobytes` | Largest requested out-of-configuration population and its canonical size; not timed | rows / bytes / decimal kB |
| `\ScalingSmallVolatileReadMedianMs`, `\ScalingSmallVolatileUpdateMedianMs`, `\ScalingSmallPersistentReadMedianMs`, `\ScalingSmallPersistentUpdateMedianMs`, `\ScalingMaximumVolatileReadMedianMs`, `\ScalingMaximumVolatileUpdateMedianMs`, `\ScalingMaximumPersistentReadMedianMs`, `\ScalingMaximumPersistentUpdateMedianMs` | Prepared median at the smallest and maximum fitting scaling populations, by storage/operation | ms |

The additional evidence macros are defined as follows. `\CpuGovernor` and
`\TurboSetting` are text, `\CpuClockGHz` is the fixed clock in GHz, and
`\SessionCount` counts independent sessions. `\RustProductionLines` excludes
the tests counted separately by `\RustTestLines`. `\IndexedClientLines`,
`\IndexedProofLines` and `\IndexedProofRatio` count the indexed client,
its proofs and their proof/program ratio; `\VoucherClientLines`,
`\VoucherProofLines` and `\VoucherProofRatio` have the same meaning for
vouchers. Counts are nonblank lines and do not estimate authoring time.

`\ComparisonLargeRows` is the additional near-limit population. The
`\LargeJayReadMs`, `\LargeJayWriteMs`, `\LargePgReadMs`, `\LargePgWriteMs`,
`\LargeSqReadMs` and `\LargeSqWriteMs` macros report large-state point
medians in milliseconds. The corresponding `\LargeOwnerJayReadMs`,
`\LargeOwnerJayWriteMs`, `\LargeOwnerPgReadMs`, `\LargeOwnerPgWriteMs`,
`\LargeOwnerSqReadMs` and `\LargeOwnerSqWriteMs` report the owner profile.
`\ScalingFirstKeySmallMs` and `\ScalingFirstKeyLargeMs` are first-key read
medians at the smallest and largest E5 populations, for comparison with the
last-key volatile medians. Confirm their storage-mode interpretation in the
measurement pass. `registration-table.tex` reports preparation time
minimum/median/maximum by program and storage mode; `session-spread-table.tex`
reports pooled headline medians and min–max of session medians. Both are
written under `.build/tcc/` by the measurement agent's evidence builder.

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
that window. No governor, affinity or power setting is changed by the harness.
Durable equal-state successes reuse their already durable image; changed state,
including new receipt rows, still follows file sync/rename/directory sync.

The performance follow-up is recorded in `paper/evidence/performance-report.txt`
and `performance-summary.json`, including before/after medians, inclusive
quartiles, sample counts, validation and fingerprints for all E1–E5 cases.
`latency-diagnosis.json` retains separate observer samples and syscall excerpts;
these diagnostic timings are not inputs to the headline tables.

Preparation means one-time checking and compilation; registry means the
prepared handle table. Generated filenames and macro names retain their
original registration/persistent spelling.

## Claim and reference review

A successful unchanged-state Commit updates the RAM root/response pair while
reusing the durable image. Changed states complete full-image write, file
fsync, atomic replacement and directory fsync before publication and reply;
open synchronizes the validated authoritative file and directory once.
Recovery checks configuration and identity, not a proof of recovered-root
validity. Persistence integrity remains a T1/host obligation; the voucher
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

The RLS comparison distinguishes row filtering from rejecting a program before
its first forbidden observation. The source listing copies the indexed entry
and `Policy.Rule` branches, omitting imports and helper definitions. Bend is
used so that one checked Book contains both the proofs and the functions
compiled to C; this choice does not assert superiority over Coq, Lean or F*.
The oracle generator is untrusted because its output is checked, while checker
soundness and source binding remain trusted. Agreement between the related
checker modes is not independent evidence of logical soundness.

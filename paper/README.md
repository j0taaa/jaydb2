# TCC manuscript and defense slides

English SBC conference article by **Gabriel Jota Lizardo, PUC Minas**, with a
Portuguese Beamer defense and Portuguese speaker notes. The deck retains its
existing theme and has **22 main frames and seven appendix frames**, including
a final AI-use disclosure. The article has **16 pages including 32 references**;
it contains no appendix. Change text directly in `main.tex` and `slides.tex`.

## SBC template and build

The unmodified `sbc-template.sty` (December 2017 update) and `sbc.bst` were
obtained directly from the Sociedade Brasileira de Computação, without a mirror:

- Official archive: <https://www.sbc.org.br/wp-content/uploads/2024/07/modelosparapublicaodeartigos.zip>
- Archive members: `modelosparapublicaodeartigos/Template_SBC/template-latex/sbc-template.sty`
  and `modelosparapublicaodeartigos/Template_SBC/template-latex/sbc.bst`.
- Official SBC-authored Overleaf example: <https://www.overleaf.com/latex/templates/sbc-conferences-template/blbxwjwzdngr>

The article uses `\documentclass[12pt]{article}` and `\usepackage{sbc-template}`,
the template's title/author/address and abstract/resumo environments, Times font,
A4 page, 3 cm side margins, 3.5 cm top and 2.5 cm bottom margins, template paragraph
spacing and captions. There are no manuscript geometry/font/indent overrides.
Article citations use the template's author/year labels from BibTeX with
`sbc.bst`; `references.bib` preserves all 21 original references and adds eight
official tool references, two NVIDIA CUDA/NVRTC references and NumPy. URLs/DOIs
are in `note`/`howpublished` because the original
SBC bibliography style does not print dedicated `url`/`doi` fields. The article
uses `url` without `hyperref`, avoiding the official style's old hyperlink hook;
the vendored style remains byte-identical to SBC's archive.

```sh
make -C paper
PYTHONPATH="$JAYDB2_PY_DEPS" python3 -B -m unittest discover -s paper -p test_evidence.py -v
PYTHONPATH="$JAYDB2_PY_DEPS" python3 -m pytest paper/test_evidence.py
pdfinfo .build/tcc/output/jaydb2-tcc.pdf
pdfinfo .build/tcc/output/jaydb2-defense.pdf
```

Set `JAYDB2_PY_DEPS` to the package directory for a Python environment providing
pytest, NumPy and matplotlib (or leave it empty when those packages are already
available to `python3`). The retained GPU benchmark records NumPy 2.5.4.

Requires Python 3 with NumPy (independent GPU/E6 oracle validation), pdfLaTeX and BibTeX, plus standard Times/PSNFSS, fontenc/inputenc,
Babel (English and Brazilian Portuguese), AMS, caption, titlesec, etoolbox,
microtype, booktabs, array, url, Beamer, Latin Modern, Helvetica, hyperref (slides),
TikZ/PGF and PGFPlots packages. Verified with TeX Live 2026. The article build is
**pdflatex → bibtex → pdflatex → pdflatex**; the slides receive two pdfLaTeX passes.
BibTeX runs inside the output directory, with the paper directory on its
bibliography/style search paths. `make clean` also removes BibTeX intermediates.

All build products are ignored under `.build/tcc/`; the deliverables are:

- `.build/tcc/output/jaydb2-tcc.pdf`
- `.build/tcc/output/jaydb2-defense.pdf`

The evidence builder validates the retained experiments and generates all measured
values, table fragments and plot data. No measurement is copied into the article
or slides source. The current refresh reruns E1–E6 and the focused GPU benchmark on one frozen
engine under the fixed-clock protocol below;
the builder regenerates the derived evidence reports from the retained JSON.

## Course-regulation compliance

For PUC Minas Ciência da Computação TCC II, the manuscript follows Art. 3's SBC
LaTeX requirement and Art. 4's **10–16 pages**, counting references. Its outline
maps to the required roles in this order:

| Regulation item | Article location |
|---|---|
| I — Introduction | Section 1: context, motivation/justification, problem, general objective paragraph, specific-objective bullets, research questions, synthesis/results and roadmap |
| II — Theoretical background and literature review | Section 2: PCC, verified databases, policy systems, SQL mechanisms and trust boundaries |
| III — Methodology | Section 3: construction steps, cited/versioned tools, model, architecture diagram, executable guarantees, trusted base, applications and evaluation protocol |
| IV — Results with analysis | Section 4: E1–E6 latency, reuse, SQL comparison, verification, state scaling and certified CPU/CUDA simulation, with generated tables/PGFPlots; Section 5 discusses limitations |
| V — Conclusions and future work | Section 6: contributions, main results, explicit comparison with literature and future directions |
| VI — References | 32 BibTeX references using `sbc.bst` |

Both the English abstract and faithful Portuguese **Resumo** appear on the first
page, each with ten rendered lines, within SBC's guidance. The unnumbered
**Use of Artificial Intelligence** note before the references
states tools/models/vendors, purposes, contribution to all article sections and
slides, author responsibility and executed-data provenance (Arts. 6–9). Its source
comment `% AUTHOR: review and adjust this declaration` marks it for author review.
The advisor, Gabriel Barbosa da Fonseca, appears in the SBC author block and on
the title slide. The affiliation is ICEI, PUC Minas, Belo Horizonte–MG–Brasil.
No email, committee member or defense date is invented.

To fit the page limit, the article condenses background, model, controller,
application and repeated result prose; the full theorem inventory and numbered
T3 duties remain in `proof/README.md`. Guarantees, the formal certificate/Core
statements, all required sections and limitations remain explicit. The article
has no appendix. GPU mode keeps the same proof obligations on the sealed Book;
T2 additionally trusts Bend's CUDA runtime path, NVRTC, driver, managed memory
and GPU hardware. CUDA libraries are recorded, not pinned. Differential tests
are evidence, not proof. E1–E5 remain GPU-disabled. E6 is a volatile simulation
comparison with separately reported admission, explicit SQL timeouts and no
equivalent SQL proof/authentication claim.

For Art. 18, the **22 main slides** have approximately **2,267 spoken words**, or
**17.4 minutes at 130 words/minute**, leaving room for transitions within the
20-minute maximum. Count only notes before `\appendix`, stop each note at
**Se perguntarem:**, and exclude trailing `Fonte:`/`Fontes:` cues. Strip formatting
commands; each numerical macro counts as one spoken token. The seven appendix
frames are untimed. Rehearsal remains necessary because numerical pronunciation
and delivery vary. The main defense adds GPU admission/trust and E6 comparison;
the AI appendix names GPU/simulation implementation, orchestration and independent reviews.

The count is reproducible from the source (run at repository root):

```sh
python3 -B - <<'PYCODE'
from pathlib import Path
import re
main = Path('paper/slides.tex').read_text().split('\\appendix', 1)[0]
notes = re.findall(r'\\note\{(.*?)\}\s*\\end\{frame\}', main, re.S)
words = 0
for note in notes:
    note = re.split(r'Se perguntarem:|Fontes?:', note)[0]
    note = re.sub(r'\\(?:par|textbf|texttt|numpt|latpt|intpt|ratiopt)\b', ' ', note)
    note = re.sub(r'\\([A-Za-z]+)', r' \1 ', note)
    words += len(re.sub(r'[{}~$\\]', ' ', note).split())
print(len(notes), words, round(words / 130, 1))
PYCODE
```

Before submission, the advisor reviews the article, and the author rehearses the
defense. No committee member or defense date is assumed.

For visual QA, render every article page and slide at 60 dpi (scratch files stay
ignored in `paper/.qa/`):

```sh
mkdir -p paper/.qa/article paper/.qa/slides
pdftoppm -png -r 60 .build/tcc/output/jaydb2-tcc.pdf paper/.qa/article/page
pdftoppm -png -r 60 .build/tcc/output/jaydb2-defense.pdf paper/.qa/slides/slide
```

Inspect every PNG for clipping, captions, table/plot fit and typography. Final
`main.log` and `slides.log` must contain no undefined references/citations/macros
or overfull boxes. Count references with `rg -c '^\\bibitem' .build/tcc/main.bbl`.

## Reproducing the fresh evidence

Each benchmark JSON records its exact source commit and executable/source
fingerprints. E1–E6 and the focused GPU benchmark (including verification commands) must share the same
engine source and executable fingerprints; the historical direct-seed attempt
is retained separately. The harness uses the real serial Rust host, official Bend 2.0.39 and
BendTT, literal emitted C, Clang 19, and one native worker thread. The final protocol uses independent sessions at the nominal base clock with
the performance governor and turbo disabled. E5 uses one session with
log-spaced populations and a first-key variant. Historical frequency-scaling
measurements are excluded from the final latency evaluation. No mock engine or alternate verifier
is measured. All output values are checked. Initialization and warmups are
outside the operation samples. JSON files include raw nanoseconds (E1–E5) or milliseconds (GPU/E6), outputs,
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
database for each E1–E3 session. The complete refresh is:

```sh
export PYTHONPATH="$JAYDB2_PY_DEPS"
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B paper/bench/refresh.py'
python3 -B paper/evidence.py
# Optional standalone figures (Matplotlib):
python3 -B paper/bench/gpu_chart.py
python3 -B paper/bench/simulation_chart.py
python3 -B -m unittest discover -s paper -p test_evidence.py -v
python3 -m pytest paper/test_evidence.py
make -C paper
```

`refresh.py` requires a clean worktree, runs `make build`, then runs each of the
following under `paper/bench/fixed-clock.sh`, still holding the outer heavy lock:

| Evidence | Command inside fixed-clock wrapper |
|---|---|
| E1 | `python3 -B paper/bench/run.py latency` |
| E2 | `python3 -B paper/bench/run.py prepared` |
| E3 | `python3 -B paper/bench/run.py comparison` |
| E5 | `python3 -B paper/bench/run.py scaling` |
| E4 | `python3 -B paper/bench/run.py verification` |
| Source inventory | `python3 -B -m paper.bench.source_sizes --update` |
| Focused GPU | `python3 -B paper/bench/gpu_programs.py --output paper/evidence/gpu-programs.json` |
| E6 | `python3 -B paper/bench/simulation.py --output paper/evidence/simulation.json` |

After every command it reads back all CPU settings, requiring `powersave`,
`balance_performance`, and `no_turbo=0`. Any harness/gate failure stops the refresh.
It retains per-command logs, durations, source revision, raw-file hashes and CPU
readbacks under `.build/paper-bench/refresh-*`. Outputs are staged there and each
tracked evidence path restored to HEAD before the next measurement, so every
metadata block starts with `dirty: []`. Nothing is committed between measurements.
The legacy `base_commit` field identifies the harness origin; `commit` records
the measured revision (the current frozen engine was branched from `685bb67`).
The inventory is merged into the fresh E4 timings after collection. Only after
all commands and `python3 -B paper/bench/check-clock.py` pass are the staged raw
JSON files published together; `paper/evidence/refresh-log.json` retains the audit.
The first integrated refresh used this same output-staging procedure, with its
source-inventory invocation collected after the other benchmarks on the same
clean revision. Historical `scaling-seed-attempt.json` is retained separately.

The direct GPU scripts above do not acquire a nested lock. If using the nested
make targets (`benchmark-gpu`, `benchmark-simulation`, `test-gpu`, `smoke`) instead:

```sh
bash -c 'exec 9>/tmp/jaydb2-experiments-heavy.lock; flock 9; ulimit -s unlimited; export JAYDB_HEAVY_LOCK_FD=9; make test-gpu'
```

Never export an empty `JAYDB_HEAVY_LOCK_FD`. Use the same nonempty inherited
file descriptor for nested targets. Default E1–E5 metadata say GPU off; focused
GPU settings are in each run's backend/threads/artifact, and E6 records all modes.

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

`verification.json` retains fresh successful `make verify-contract`,
`make verify`, and `make test` wall times and full output under the same
fixed-clock policy. These are single observations, without quartiles.
The `detailed_sizes` inventory separates the Rust host's nonblank physical
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
and Voucher's `ClientProof.bend`. RLS counts `applications/rls/Client.bend`
against `ClientProof.bend` plus `Completion.bend`; shared ownership, directory
and judgment/publication proofs are excluded by the same scoped definition. Ratios are proof/program nonblank lines.
These local client-certificate counts exclude reusable library/kernel proofs,
model/schema/seed files, shared application ownership proofs, and the separate
voucher functional theorem suite; they are scoped client integration costs,
not complete application correctness-proof sizes. `detailed_sizes` lists every
included file and its count. Counts of `law` declarations, proof definitions
and named theorem witnesses remain distinct syntactic facts.

E6 (`simulation.json`) compares the certified application on CPU-1, CPU-16 and
CUDA with PostgreSQL PL/pgSQL and SQLite recursive CTE, without Python UDFs.
Runtime arguments vary paths/steps while all engines store identical Alice/Bob
parameter rows. It has one session per backend, one excluded warmup and three
measured samples per completed size. Preparation (both checkers, compilation and
optional cubin prebuild) is a separate single observation. JayDB2 includes
encoding/transport, fresh authentication, integrity checks, fresh process/device
startup, simulation, publication, decoding and inspector emission; SQL includes
execute/fetch, in-database reads/computation/upsert. Complete states/tables and
scalar Python/NumPy oracles are checked outside timing. SQL cancellations are
retained as timeouts; later sizes are not run, never extrapolated. RAM/TEMP/
`:memory:` storage makes this a volatile compute comparison, with no equivalent
SQL admission/authentication or durability claim. GPU clocks are unfixed; device,
driver and resolved NVRTC library versions/hashes come from retained artifacts.

The focused GPU benchmark retains separate native-worker and complete-request
trials (not additive phases), both with one excluded warmup and three samples.
Its independent U32 oracle evaluates every seed/round; complete published states
are checked. The evidence builder recomputes GPU and E6 oracles at every measured
size, checks complete state histories and SQL controls, raw medians/ranges,
backend/size/sample coverage, fixed CPU policy, fixture and shared engine
fingerprints, cubin/library provenance and timeout ordering. Corruption tests
exercise these checks. NumPy is required for this validation; matplotlib is
optional for standalone figures. Build/report paths remain ignored.

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
subphases and must not be added to them. BendTT and C generation/build now
overlap: their diagnostic durations must not be summed as exclusive wall time.
The ordinary `OtherSeconds` macros subtract admission wall time and worker
time from the round trip; they include the remaining host/communication work. The oracle-soundness law's share is
included in whole-Book checking: the pinned APIs expose no per-law timer.
Successful C/native receipts are withheld until both official checkers accept
the same sealed Book and seals/artifact hashes verify. `stage.mjs` checks those
hashes before releasing a path. T1 relies on this release barrier independently
of cleanup. This overlap applies to ordinary admission and preparation.
`integration-validation.json` was removed: it was a validation receipt, not a
measurement input consumed by `evidence.py`. Measurement JSON is unchanged.
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
| `\OrdinaryReadCheckingSeconds`, `\OrdinaryIndexedCheckingSeconds`, `\OrdinaryVoucherCheckingSeconds` | Median of primary + BendTT diagnostics per call; overlaps native build, not additive with it | s |
| `\OrdinaryReadCompilationSeconds`, `\OrdinaryIndexedCompilationSeconds`, `\OrdinaryVoucherCompilationSeconds` | Median of C emission + compilation per call; overlaps BendTT checking | s |
| `\OrdinaryReadWorkerMs`, `\OrdinaryIndexedWorkerMs`, `\OrdinaryVoucherWorkerMs` | Median worker phase wall time | ms |
| `\OrdinaryReadOtherSeconds`, `\OrdinaryIndexedOtherSeconds`, `\OrdinaryVoucherOtherSeconds` | Median per-call round trip minus admission wall time and worker; includes remaining host work/communication | s |
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

### Derived macros for preparation phases, sizes and ratios

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

### Integrated RLS and host-duty evidence macros

| Macro | Meaning / unit |
|---|---|
| `\RlsClientLines` | RLS client program nonblank lines (Client.bend) |
| `\RlsProofLines` | RLS scoped certificate/termination nonblank lines (ClientProof.bend + Completion.bend) |
| `\RlsProofRatio` | Scoped RLS proof/program line ratio |
| `\RlsNegativeFixtures` | RLS causal negative fixtures checked in both official modes (separate from core NegativeFixtures) |
| `\RlsNativeResponses` | Exactly checked responses in the complete native RLS session |
| `\HostDutyCount` | Numbered T3 duties read from proof/README.md; eight regrouped items do not reduce the previous eleven trust obligations |
| `\OrdinaryReadAdmissionSeconds`, `\OrdinaryIndexedAdmissionSeconds`, `\OrdinaryVoucherAdmissionSeconds` | Admission wall time, including overlapping checker/native-build phases (s) |
| `\RlsNonblankLines` | All maintained top-level RLS Bend source lines, including schema/laws/seed and domain proofs; generated .build packages excluded |

### GPU and E6 macro contract

All values and table cells come from validated raw evidence; medians are not kernel times.

| Macro | Meaning | Unit |
|---|---|---|
| `\GpuDevice` | Measured CUDA device | text |
| `\GpuDriverVersion` | Recorded NVIDIA driver version | version |
| `\NvrtcLibraryVersion` | Resolved libnvrtc shared-library version (not pinned) | version |
| `\GpuCorpusMiB` | Requested CUDA managed-memory corpus | MiB |
| `\SimulationRepeats` | E6 measured calls per completed backend/size | samples |
| `\SimulationWarmups` | E6 excluded warmups per backend/size | calls |
| `\SimulationSessionCount` | E6 sessions per backend | sessions |
| `\SimulationLargestPaths` | Largest E6 path count | paths |
| `\SimulationLargestSteps` | Largest E6 steps per path | steps |
| `\SimulationMeasuredSamples` | E6 completed measured samples across all backends | samples |
| `\GpuRepeats` | Focused GPU samples per size/backend/timing boundary | samples |
| `\SimulationCpuOnePreparationMs` | E6 single preparation observation; excluded from call times | ms |
| `\SimulationCpuSixteenPreparationMs` | E6 single preparation observation; excluded from call times | ms |
| `\SimulationCudaPreparationMs` | E6 single preparation observation; excluded from call times | ms |
| `\SimulationSmallCpuOneMs` | E6 small complete cpu-1 request median | ms |
| `\SimulationLargeCpuOneMs` | E6 large complete cpu-1 request median | ms |
| `\SimulationSmallCpuSixteenMs` | E6 small complete cpu-16 request median | ms |
| `\SimulationLargeCpuSixteenMs` | E6 large complete cpu-16 request median | ms |
| `\SimulationSmallCudaMs` | E6 small complete cuda request median | ms |
| `\SimulationLargeCudaMs` | E6 large complete cuda request median | ms |
| `\GpuSmallCudaNativeMs` | Small focused CUDA native worker median; includes process/device startup | ms |

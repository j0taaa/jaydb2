# Optional ordinary Bend library

## Revisions and dependency boundary

Base: `5925c57febd978d44fa24000233647a59e7898a6`; original reference:
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`. Branch: `experiment-library`.
Foundational checkpoint: `91f8a2dee8e23c14bcf44eb7a0303e2ce93752b8`; corrected/expanded checkpoint: `d8b019c14c5526bb4b23b2c14098e22ceb254252`;
coordinator-accepted foundation gate: `d85618b4608077ce1677417d21bccd53a4105824` (both official checkers).
The original validated implementation checkpoint was
`b19e265c547fab757df6d0a8200c6c8814e949ac`. The audited repair implementation is
`0cd40ddb1e76c40b9327a87cf7542414ba2d7d8a`; sorting/content repair checkpoint:
`d1342e2a8b354ae5e75f4bd8447fbec91bc43701`. The parent independently inspected
and accepted both targeted repairs (A2 sorting, A3 certified index flow).
The final repair commit changes only this report and the library README.

Only `src/ReadOnly.bend` was imported from accepted concurrency source commit
`b6ef4a6681906859fdcdd4caf5b85b8fd318dcd8`, using `git restore --source=... --
src/ReadOnly.bend`. Its exact SHA-256 is
`e525c1eec917cca6e139f661c5aab9a9c64fd5375faea9fd980adb585632ed0a`.
The coordinator independently dual-checked that file before authorizing import.
This dependency is the predicate/API alone. No host batching, ReadBatches proof,
storage, admission or scheduling changes were imported or claimed.

The pinned official Bend 2.0.39, BendTT, compiler sources and emitted C are
unchanged. `.tools` is an ignored symlink to the shared immutable installation.
Build, generated proof packages, native binaries, runtime sessions and temporary
state are local to this checkout under `build/library` (and ordinary `target`).

## Exact supported inventory

| Module | Implemented behavior |
| --- | --- |
| `Value` | Full two-U32 `Int64`; typed integer/text/boolean/list-shape decoding, integer encoding and pure structural value equality. |
| `Record` | Canonical validated record construction, unchecked raw construction and field deconstruction. Rejects duplicate/unordered/invalid field names and invalid nested values through `make`. |
| `Key` | Injective reversible encoding of an arbitrary String list, preserving empty components, Unicode and delimiter characters. Strict malformed/trailing-input decoder. |
| `Int64` | Exact signed comparison; checked add/sub/mul/divmod/increment/decrement; explicitly named wrapping add/sub. Division truncates toward zero; signed remainder follows dividend. |
| `Read` / existing `Query` | Ordinary existence/count/key reads; canonical field selection, missing-versus-present-absent handling, projections and CPS finite traversal/filter-map. |
| `Sequence` | Pure filtering, stable insertion sorting, grouping, offset/size pagination, length and response-list construction. |
| `SortProof` | Arbitrary-predicate count and per-value multiplicity preservation; independent all-pairs sortedness under explicit order obligations; fully discharged task-order instance. |
| `Aggregate` | Checked signed sum/count, seeded and empty-aware min/max, integer average. |
| `Relation` | Pure nested-loop inner and left joins retaining duplicate matches; referential-law template in `TableLaws`. |
| `Action` / `Mutation` | Ordered batch row writes, batch removals, column patches, insert-if-absent, predicate replacement, actual-cell compare-and-replace of a complete row, checked counters and incrementing sequences. |
| `Index` | Ordinary-table unique claims/direct lookups, nonunique/composite entries and equality scans, explicit removal/replacement maintenance and complete rebuild. |
| `Summary` | Checked count/total computation and explicit ordinary-table materialization. |
| `Laws` / `TableLaws` | Per-operation permission and whole-continuation finite-depth composition; exact-index/reference law templates, explicit stable-only versus every-prefix invariant phases. |
| `ReadProgram` | Closed cell/selection constructors and a text-key program factory; finite whole-continuation read-only proofs against the accepted predicate. |

`library/README.md` documents all accesses, schemas, examples, algorithm order,
preconditions and transaction contracts. The ordinary task example adds commands:

```text
["pair", "t1", "t2", false]
["open", "t1", "t2"]
["inspect", "t1"]
["insert", "once"]
["replace_open", "once"]
["cas", "once", true]
["drop", "once", "missing"]
```

These are ordinary real submissions with independently proved administrator
certificates. Read-only construction does not grant access to another user.
The full QueryClient contains writes and remains an ordinary program; this
branch does not introduce an execution-route flag or refuse existing programs.

## Contracts, proofs and assumptions

No contract, primitive, stored scalar domain, canonical limit or permission grant
is changed. All helpers construct normal Actions or operate purely on already
obtained data. Conditional writes, index/summary maintenance, traversal and joins
remain within the caller's existing transaction. Every actual access, including
existence, enumeration, missing/filtered reads and failed writes, remains subject
to installed administrator laws at every prefix. Success publication and rollback
remain the existing host behavior.

`Laws.Safe` is parameterized by the application's actual permission proposition.
`reads` requires a permission proof for every field and the entire continuation;
`write_rows` requires one for every row plus the continuation. The actual task
`Proofs.Safe` instantiates it with `Policy.Allowed`, and QueryClientProof uses
both reusable constructors. The existing ownership/prefix/final-publication
proof then connects those obligations to the ordinary certificate. No generic
permission, assumed certificate, assumed final validity or runtime final-state
check replaces these proofs.

General functional proof targets:

- `Value.integer_roundtrip`, `Record.fields_roundtrip`.
- `Key.segment_roundtrip`, `Key.roundtrip` with arity fuel, `Key.injective` for
  all String lists. Public length-fueled decode also has explicit malformed,
  delimiter and Unicode examples; no arbitrary public-decoder length lemma is
  claimed.
- `Int64.add_success_under_no_overflow` / `add_rejects_overflow` and corresponding
  subtraction equations; `signed_success` / `signed_rejected`, conditional
  `mul_success`, and division-by-zero rejection. These prove two-word API
  outcomes under the stated bit predicates. The earlier `Matches` property is
  supplementary and does not alone establish successful computation.
- `Sequence.insert_length`, `sort_length`, `take_all`, `drop_all`, `first_page`.
- `Laws.reads`, `write_rows`, `finite`; existing `Proofs.append_extends`,
  `read_continuation`, `read_then_filter`, `read_then_refuse` retain actual events.
- `ReadProgram.cell_readonly`, `fields_readonly`, `select_readonly`,
  `program_readonly`: finite restriction for **every** Return continuation and
  (for Program) every context and argument. No recursive syntax lowering/bind.

`Behavior.bend` proves representative actual functional traces/results for
sort/page/filter/group, join multiplicity and missing matches, aggregate signs
and overflow, counter prefix/carry/overflow, compare mismatch/success, unique
conflict, nonunique rebuild/query, retention of filtered index reads, and exact
full-width/invalid-field read-program behavior. Original library trace and
rollback proofs remain in `library/VERIFY.bend`.

`TableLaws` templates do not generate certificates. Applications must prove
that their supplied index entries/summary inputs correspond to business data.
The audited `applications/indexed` example now installs the actual ExactIndex/
OnStable template and proves such an ordinary application certificate. `OnStable`
explicitly permits intermediate inconsistency and requires it in Stable and
successful Closed phases; use `OnEveryPrefix` if intermediate inconsistency is
forbidden. All other installed laws continue to apply. The original contract's
bridge to the pinned compiler, actual process effects, bytes, cleanup and
publication remains a trusted integration boundary; these helpers add no host
or filesystem effects.

There is no claimed general signed mathematical correctness theorem for the
multiplication/division algorithms. Sorting now has general content preservation
and an independent all-pairs sortedness theorem under explicit transitivity and
totality proofs; the completed-task comparator has those obligations discharged.
The stronger native content oracle supplements those proofs and does not replace
permission/prefix reasoning.

## Original milestone validation

The following checks have completed:

- Cheap single-file primary `--check-only` passes for Foundation, Modules,
  Behavior, `library/VERIFY.bend`, `ReadProgram` and the generated restricted
  application proof package. This low-resource exception was explicitly
  authorized by the coordinator while the shared lock was busy.
- Locked `python3 -B tools/check.py experiments/library/Foundation.bend
  experiments/library/Modules.bend`: PASS both official `--check-only` and
  `--verdict` at the accepted `d85618b4608077ce1677417d21bccd53a4105824` checkpoint, before ReadProgram was added.
- Deliberate AlwaysNone and HiddenWrite fixtures fail primary checking at the
  intended false proof, with expected/observed type mismatches. The latter
  rejects a write behind an unreachable UnitValue continuation after a read.
- Python syntax checking and `git diff --check`: PASS.

The original focused gate **PASSED (exit 0)** at implementation checkpoint
`b19e265c547fab757df6d0a8200c6c8814e949ac`, under the shared lock:

```sh
mkdir -p build/library/tmp
flock /tmp/jaydb2-experiments-heavy.lock env TMPDIR="$PWD/build/library/tmp" make test-library
```

Actual completed results (log: `build/library/test-library.log`):

- `cargo build --locked --release`: PASS.
- `tools/check.py library/VERIFY.bend build/library/application-proof/Check.bend`:
  PASS `--check-only` and `--verdict` for **both** roots. This includes the
  accepted read-only predicate, all ReadProgram continuation proofs, original
  library trace/rollback proofs, extended functional examples and actual
  administrator permission/termination proofs.
- `experiments/library/test_negative.py`: PASS all four intended rejections:
  AlwaysNone and HiddenWrite, each in `--check-only` and `--verdict` modes.
- `experiments/library/test_arithmetic.py`: PASS **1,980** dynamic signed64
  add/sub/mul/divmod/order cases and **1,980** dynamic sort/average/summary/join/
  group cases against Python. Literal official emitted C was unchanged.
- `applications/tasks/query_check.py`: PASS the real framed host session,
  including all three prohibited-read certificate rejections and subsequent
  valid calls. Existing ordinary write-capable calls continued to succeed.

Runtime vectors include all extrema, carry/borrow,
values above native Nat48, zero/overflow/division boundaries and deterministic
random pairs. The C file is hashed before/after native compilation.

The real task test checks ownership isolation, projection/filtering, missing
rows, refusal rollback, batch writes/deletes, conditional insert/replacement,
compare success/mismatch/missing, and read-only constructor use. Three mutated
programs must receive `certificate`: another user's read followed by refusal,
another user's read-only selection, and another user's conditional read whose
comparison would fail. Subsequent correct calls check state was not changed.
The focused gate was run once to completion after the source was frozen;
no extra broad or performance suite was run. `make test`, `make test-demo-web`
and the separate full `make verify` target were not run in this branch; the
focused target itself checks original and extended library proofs with both
checkers. Active/historical contract manifests and pinned toolchain hashes are
checked by `tools/check.py`. The original report commit `66bd2995648a38fc0c9cc9521090f90dc0ec29c6` changed
documentation only relative to that original implementation checkpoint.

## Costs and limitations

No performance benchmark was run. Sorting is O(n²), grouping O(n × groups),
joins O(left × right); nonunique indexes enumerate and read all index entries.
Unique lookup uses direct ordinary row access. Counters cost a read and write;
conditional writes cost a read plus an optional write; rebuild enumerates,
removes and replaces every index row. All those accesses require permissions.

Aggregates use a right fold and reject intermediate signed64 overflow even if
a different summation order would fit. Average truncates toward zero. Missing
counters are not implicitly initialized. List sizes and offsets are Nat, never
conversions of the stored integer domain. Typed list decoding validates shape;
use `Data.value_valid` to validate arbitrary nested values. Raw record helpers
have documented preconditions.

Group items retain input order; groups are ordered by descending last occurrence.
Pagination operates on each current obtained list; separate calls observe
successive current snapshots, without historical/stable-pagination guarantees.
Index schemas and per-index composite arity are explicit; there are no automatic
triggers or implicit permission proofs. Advanced ordered/range indexes remain a
later milestone. Full text, geospatial and a query optimizer are excluded.
Idempotency/receipt logic belongs to its independent experiment and is not
duplicated here. Host concurrency and prepared read-only routing are also
outside this library branch; only their accepted predicate file is reused.


## Independently audited repairs: A2 sorting and A3 certified index flow

### Sorting contracts and content tests

`library/SortProof.bend` adds the following checked general contracts without
changing the sorting algorithm or defining sortedness in terms of its output:

- `insert_content` / `sort_content`: arbitrary Boolean-predicate counts (with
  a dynamic value environment) are preserved. No ordering assumption is needed.
- `sort_occurrences`: for every supplied value and arbitrary input list, the
  count using structural `Value.equal` is preserved, including all duplicates.
- `After` / `Sorted`: an independent all-pairs ordering predicate. Every earlier
  element is <= every later element under `Le(a,b) = not less(b,a)`.
- `insert_sorted` / `sort_sorted`: prove that predicate for arbitrary lists when
  the caller supplies explicit transitivity and totality proofs for `Le`.
- `completed_trans` / `completed_total` / `completed_sorted`: fully discharge
  those order obligations for incomplete-before-complete task values/records.

`CollectionRuntime.bend` and `test_collections.py` add **250** dynamic native
content cases over 50 input pairs, with lengths 0 through 80, empty/singleton,
reverse order, mixed duplicates, and forty equal keys. Sorting compares every
key/identity payload to stable Python sorting. Inner/left joins compare every
actual left/right pair (including duplicate and unmatched matches). Grouping
compares every group key and complete member identities/order. Counts alone are
not the oracle. The literal official emitted C is hashed before and after
compilation and remains unchanged.

Actual locked checks: `tools/check.py --timeout 120 library/SortProof.bend`
**PASS both official checkers** (`build/library/sort-check.log`); native
`experiments/library/test_collections.py` **PASS 250 cases**
(`build/library/repair-native.log`). These repaired sources are committed at
`d1342e2a8b354ae5e75f4bd8447fbec91bc43701`.

### Actual indexed business application

`applications/indexed` implements a small per-user availability index, rather
than leaving ExactIndex/OnStable as unused templates. It supports two fixed
principals (Alice/Bob), each with one Boolean business row and a separate
ordinary index table. `Model.project` maps the business row to
`Index.entry(key, [ready-or-busy], key)`.

The installed `Policy.Rule` requires business/user layout and per-access scope
at **every prefix**. Layout deliberately permits arbitrary index-row lists while
executing. Independently installed `Policy.IndexRule` uses the real
`TableLaws.OnStable(ExactIndex)` predicate for BOTH users: exact projection in
Stable and successful Closed phases, explicitly permitting transient missing/
stale indexes. `CheckedActions.Safe` follows the **actual** `Data.operate` result;
its terminal obligation is `Model.Indexes(working)`. `safe`, `execution_trace`
and publication lemmas connect those concrete proofs to ordinary
`Requirements.Certifies`, the original technical validators and stable validity.
No source allowlist, runtime final-state guard, special authority, or assumed
final-invariant certificate is introduced.

Real application operations:

- `["set", bool]`: `Index.maintain`, followed by the business write.
- `["query", bool]`: genuine `Index.lookup_many` tag-to-matching-target query;
  returns `["item"]` or `[]`, with every enumerated/filtered read authorized.
- `["rebuild"]`: reads business availability, then calls ordinary `Index.rebuild`
  to enumerate, remove and reconstruct the index from that observed value.

`ClientProof.certify` and its helpers quantify over every valid initial state,
context, argument and observation depth. The ordinary `B.certificate` wrapper
instantiates those helpers with the actual `Instance.context()` and
`Instance.arguments()` for each request; its binding is concrete, rather than
the prepared protocol's universal-certificate target. The proof derives an initial canonical
witness from the installed Layout AND ExactIndex laws, proves each real
transition, and proves exact row equality at completion. `Completion` and
`B.terminates` handle arbitrary states (including invalid ones) and arbitrarily
long finite key lists with an actual-return-dependent finite witness. They do
not assume that enumeration returns the valid-state singleton or treat a host
quota as a termination proof.

The adapted negative controls in `negative_cases.py` are substantive:

- **Omitted maintenance:** actual implementation writes only business data;
  the proof prefix is adapted to that single write and its actual working
  layout. `permitted_valid_state` and `permitted_all_prefixes` independently
  prove ordinary permissions on ALL valid initial states and ALL observation
  depths. Full certification fails at `set_alice`'s terminal exact index-row
  equality (old indexed value versus the new projected value).
- **Forged maintenance:** actual implementation writes a schema-valid index row
  targeting `forged`; the operation/layout proof is adapted accordingly.
  Its ordinary permissions and all-prefix theorem PASS independently; full
  certification fails at the terminal exact row equality (`forged` vs `item`).
- **Forbidden index read:** Alice's query uses Bob's index. Certification fails
  at `query_alice`'s FIRST permission check, `False == True`, even if the query
  would eventually filter the entry out.

Each positive permission-only control and each intended full-certificate
failure is checked in BOTH official modes. Generated roots and exact diagnostics
are reproducible under `build/library/indexed-{omitted,forged,forbidden}*`;
`indexed-*-check-only.log`, `indexed-*-verdict.log` and `indexed-host.log` retain
intended failure locations. These are adapted proofs, not unrelated stale
certificates. The real host rejects all three and subsequent successful queries
verify neither principal's published state changed.

### Accepted shared host prerequisite and final focused gate

Cherry-picked the audited shared runtime-policy fix
`b7e873cb8e3638de23313ff3655d0feedfa2e4e0` as
`166880458b8c6028f280f3276e69184406e3049b`, plus test-only immutable-fixture followup
`c39bebbd0a9b64380dd10cdeea9112b82b52d5fe` as
`805940ee58691cfebda17cb5561b0171d13cadea`. The CPU native runner clears inherited
`BENDRTS`, preserving the fixed host runtime policy. No GPU feature was merged.
The indexed host session deliberately inherits `--gpu-build --help`, so actual
successful business/index requests also exercise the repaired final-source host.

The final focused gate **PASSED (exit 0)** at exact implementation source
`0cd40ddb1e76c40b9327a87cf7542414ba2d7d8a`:

```sh
flock /tmp/jaydb2-experiments-heavy.lock env TMPDIR="$PWD/build/library/tmp" bash -c '
set -e
cargo test --locked
cargo build --locked --release
python3 -B tools/check.py --timeout 120 experiments/library/Behavior.bend
python3 -B applications/indexed/run_check.py'
```

Actual evidence in `build/library/indexed-gate.log`:

- Cargo **8/8 PASS**, including inherited runtime policy and fixed argv tests
  with the accepted immutable fixture; release build **PASS**.
- Changed Index behavior root **PASS both official checkers**.
- Full actual indexed certificate, termination and seed root **PASS both modes**.
- Omitted and forged ordinary permission/all-prefix roots **PASS both modes**.
- All three full negative controls **correctly rejected in both modes** at
  intended index-equality/first-permission targets.
- Real restricted host session **PASS**: both principals' updates, matching and
  nonmatching index queries, rebuilds, all three certificate denials and
  unchanged-state followups under hostile inherited `BENDRTS`.

The parent independently inspected the complete proofs, diagnostics and real
session output and accepted both A2 and A3. No further code or heavy reruns were
requested. Only README/REPORT documentation changes follow that validated source.
Arithmetic, contracts and unrelated integration/performance suites were not
repeated for this targeted repair. The original generic multiplication/division
algebra limitation remains disclosed; no arithmetic bug or arithmetic change was
introduced. The certified example is intentionally limited to the stated two
principals and one Boolean business row each; it does not generate invariant
proofs automatically for arbitrary applications. Other prior scope/algorithmic
cost limits remain unchanged.

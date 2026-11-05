# Optional ordinary Bend library

## Revisions and dependency boundary

Base: `5925c57febd978d44fa24000233647a59e7898a6`; original reference:
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`. Branch: `experiment-library`.
Foundational checkpoint: `91f8a2dee8e23c14bcf44eb7a0303e2ce93752b8`; corrected/expanded checkpoint: `d8b019c14c5526bb4b23b2c14098e22ceb254252`;
coordinator-accepted foundation gate: `d85618b4608077ce1677417d21bccd53a4105824` (both official checkers).
The validated implementation checkpoint is
`b19e265c547fab757df6d0a8200c6c8814e949ac`.

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

`TableLaws` templates have no certificates. Applications must prove that their
supplied index entries/summary inputs correspond to business data. `OnStable`
explicitly permits intermediate inconsistency and requires it in Stable and
successful Closed phases; use `OnEveryPrefix` if intermediate inconsistency is
forbidden. All other installed laws continue to apply. The original contract's
bridge to the pinned compiler, actual process effects, bytes, cleanup and
publication remains a trusted integration boundary; these helpers add no host
or filesystem effects.

There is no claimed general signed mathematical correctness theorem for the
multiplication/division algorithms, or general sortedness theorem for an
arbitrary comparator. Concrete proofs and an independent dynamic native oracle
provide additional functional evidence; they are not substituted for the
permission/prefix proof.

## Validation

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

The final focused gate **PASSED (exit 0)** at implementation checkpoint
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
checked by `tools/check.py`. The final report commit changes documentation only
relative to the validated implementation checkpoint.

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

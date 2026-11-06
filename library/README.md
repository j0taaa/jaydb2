# Optional Bend access helpers

These are ordinary Bend modules over `Semantics.Action` and `Data.Operation`.
They receive no database state, add no primitive or policy, and are not imported
by the kernel or the ordinary task client. Administrators still choose arbitrary
laws; applications prove those laws for every actual operation and prefix.

| Entry point | Behavior |
| --- | --- |
| `Query.select(collection, key, fields, done)` | Read each requested field with `ReadCell`, then call `done(Selection)`. |
| `Query.field(record, name)` | Pure lookup in an already obtained canonical record; returns `Some(VAbsent)` for a present absent value, `None` for a missing field or malformed record. |
| `Query.filter_map(~Env, ~visit, env, keys, done)` | Visit supplied keys in order; `None` filters a result and `Some(value)` projects it into the returned `Value` list. |
| `Action.define_rows(collection, rows, done)` | Perform each existing `DefineRow` in order, then continue with the supplied terminal/action. |

`Selection` distinguishes `Selected(record)`, `MissingRow`, `InvalidFields`,
and `UnexpectedReturn`. A legitimate `Cell(VAbsent)` becomes a present record
field. Selection requires valid field names in strictly increasing canonical
order. Duplicates, invalid names and unsorted lists produce `InvalidFields`
before any access; they are never silently dropped or sorted. An empty selection
returns an empty record without testing row existence. Use `ViewExistence` if
that observation is required.

Selection performs all requested reads, including after `RowAbsent`; actual
data-operation failure stops execution normally with a data error. Unsupported
columns and missing collections therefore follow the existing operation rules.
The helper does not infer column types: the caller handles unexpected values
when projecting. Valid stored scalar values retain their original types.
Internal decomposition helpers such as `read_fields` assume the validated field
list; use `select` when accepting input.

`filter_map` accepts an ordinary closed Bend template visitor with a separate
`Data` environment because Bend closures are affine. The visitor has type
`Env -> String -> (Maybe<&2, Value> -> Action) -> Action`. It can use `select`
and other basic operations before calling its continuation. Key order and
repetitions are preserved. Obtain keys with ordinary `EnumerateKeys` if needed;
that access has its own proof obligation. Returned records/lists are response
values, not new stored column kinds. As with any application formatting code,
the visitor must produce valid projected values.

`define_rows` neither starts nor publishes a transaction. Later operations see
earlier working-state changes. Existing success publication, refusal rollback,
and data-error rollback apply to the entire call. It checks the expected
`UnitValue` write return; a mismatched return refuses. Schema/type validation and
all permissions remain those of the existing operations. Writes are not
preceded by hidden reads.

## Proofs and a real task flow

`Proofs.bend` supplies small general equations: an actual observed operation
appends its read event before continuing, and pure filtering or refusal retains
that event and all prior history. The premise identifies `Data.operate`'s actual
result; it does not assume authorization of an operation or transaction.
`append_extends` states that appending an event retains the prior prefix.
`VERIFY.bend` checks a concrete four-read filtered projection, including both
reads of the excluded row, canonical-input boundaries, absent data, and a failed
second write with publication rollback.

The optional [task client](../applications/tasks/QueryClient.bend) supports:

- `["pair", "t1", "t2", false]`: write two owned rows in the same transaction.
- `["open", "t1", "t2"]`: read `completed` and `title` for both keys, omit completed/missing tasks, and return title-only canonical records.
- `["pair", "t2", "t3", true]`: perform both writes and refuse, publishing neither.

Its proof uses the existing task ownership/read/write laws and per-operation
permission composition. The original task client and its proof remain intact.
The example takes two caller-supplied keys to keep the flow small; the library
traversal itself accepts any finite key list. This is not a query optimizer or
a general certificate generator.

```sh
python3 -B tools/check.py library/VERIFY.bend
python3 -B tools/bend.py library/VERIFY.bend
python3 -B applications/tasks/query_check.py
python3 -B applications/tasks/check.py
```

The query check explicitly copies the modules into its temporary administrator
directory, adjusts only relative imports to the ordinary flat package, and
imports them from configuration. The normal public dependency closure freezes
and hashes them. Submitted program/proof/source bindings remain actual; database
state is never placed in verification files. No production staging change is
needed. Each positive request uses official checking and native execution. A
foreign-table read followed by refusal, submitted with the positive proof,
must be rejected by the actual primary checker.

## Official limitation: general bind

A general structural bind over the existing higher-order `Action` was attempted:

```bend
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S

def bind(action: S.Action, next: D.Value -> S.Action) -> S.Action:
  match action:
    case S.Finish{value}: next(value)
    case S.Refuse{value}: S.Refuse{value}
    case S.Access{operation, resume}:
      S.Access{operation, r => bind(resume(r), next)}
```

Saving this as `library/BindAttempt.bend` and running
`python3 -B tools/bend.py library/BindAttempt.bend --check-only` with official
Bend 2.0.39 rejects the recursive call:

```text
- expected : a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)
- observed : bind
Location: bind
```

`define_rows` instead recurses over a structural `List<Row>`, which the original
checker accepts. No checker/compiler/runtime sources or fuel settings changed.

## Extended ordinary library

The experiment adds the modules below. These remain opt-in ordinary modules,
with the same `Action`/`Return` CPS interface. No general `bind`, special access,
state handle, trigger, grant, or assumed certificate is introduced.

| Module | Public operations and behavior |
| --- | --- |
| `Value` | Typed `integer`, `text`, `boolean`, structural `list` decoders; exact two-word `Int64`, `int_value`, pure structural `equal`. |
| `Record` | `make(fields)` validates canonical field order/names/nested values; `raw` and `fields` are unchecked construction/deconstruction with a general roundtrip proof. |
| `Key` | `encode(parts)` produces an injective reversible composite row key; `decode` rejects malformed/trailing characters. Empty components, delimiters and Unicode are preserved. |
| `Int64` | Signed comparison, checked `add`, `sub`, `mul`, `divmod`, `increment`, `decrement`; explicit `wrapping_add`/`wrapping_sub` for bit arithmetic. |
| `ComparisonProofs` | Optional structural-equality reflection and actual signed-comparison strict total order; imports no new runtime behavior. |
| `Read` | Typed CPS `keys`, `exists`, `count`, each performing exactly one ordinary operation; unexpected returns refuse. |
| `Sequence` | Pure filtering, stable insertion sorting, grouping, offset/size pagination, length, conversion to a response `Value` list. |
| `SortProof` | General content/occurrence preservation and independent all-pairs sortedness under explicit order proofs; discharged incomplete-before-complete task order. |
| `Aggregate` | Checked signed64 `sum`, `count`, integer `average` (toward zero), seeded `minimum`/`maximum`, empty-aware `min_value`/`max_value`. |
| `Relation` | Nested-loop `inner` and `left_join` over obtained values; duplicate matches are retained, unmatched left rows use `VAbsent` as the right value. |
| `Mutation` | `insert_if_absent`, predicate-based `replace_if`, `compare_exchange` of one cell followed by a complete row replacement, `remove_rows`, `columns`, checked `counter_add` and `next`. |
| `Index` | Ordinary-table unique claims/keyed lookups; derived entries and explicit full-table `scan_equal`; explicit `maintain` and `rebuild`. |
| `Summary` | Checked count/total computation and explicit ordinary-table summary storage. |
| `Laws` | Parameterized per-operation `Safe`, per-field `reads`, per-row `write_rows` and finite-depth proof composition; application permissions are mandatory inputs. |
| `TableLaws` | Propositional exact-index and relation-reference templates, with explicit `OnStable` or `OnEveryPrefix` phase behavior. |

Typed list decoding checks list shape; callers needing fully validated nested
values also use `Data.value_valid`. `Record.make` already performs that validation.
The raw decomposition functions have no database access and do not certify data.

Examples in Bend (imports abbreviated):

```bend
# Composite key with unambiguous empty and delimiter-containing components.
Key.encode(["alice", "request:17", ""])

# Canonical records reject duplicates and incorrect ordering.
Record.make([D.Field{"a", D.VAbsent{}}, D.Field{"z", D.VInt{2147483648, 0}}])

# Full signed64 carry; Some(Int64{1,0}), not a native Nat conversion.
Int64.add(Value.Int64{0, 4294967295}, Value.Int64{0, 1})

# Caller proves both ViewExistence and the conditional DefineRow permissions.
Mutation.insert_if_absent(collection, row, inserted => S.Finish{D.VBool{inserted}})

# Compare an actual cell; if equal, replace the entire supplied row.
Mutation.compare_exchange(collection, replacement, "version", expected,
  changed => S.Finish{D.VBool{changed}})

# Ordinary unique-index claim. Continue with the business write only if claimed.
Index.claim(index_collection, ["email", email], primary_key,
  claimed => continue_business(claimed))
```

### Access and transaction contracts

`Read` emits the named operation even if the eventual caller filters or refuses.
`Query.select` emits one `ReadCell` per requested canonical field, including
reads after `RowAbsent`; an empty field list does not inspect row existence.
`filter_map` emits exactly its visitor's accesses, in supplied key order.
`Sequence`, `Aggregate`, `Relation`, `Value`, `Record` and `Key` are pure and only
operate on already supplied data. Sorting/grouping/joining cannot authorize the
reads used to obtain that data.

`Mutation.insert_if_absent` first emits `ViewExistence`, then a `DefineRow` only
if absent. An occupied key returns false even if its contents would be identical.
`replace_if`/`compare_exchange` first emit `ReadCell`, then optionally `DefineRow`.
A missing row never equals a present `VAbsent`. `columns` emits `DefineColumn`
for each supplied field in order; it does not create absent rows. `remove_rows`
emits `RemoveRow` even for absent keys, preserving ordinary operation semantics.
Counters first read the named cell, then write `DefineColumn` only for a present
integer whose checked addition succeeds. Missing/noninteger/overflow refuses;
there is no implicit initialization. `next` returns the incremented value.

Each index table has required text columns `id`, `target`, `value`, keyed by
`id`. Unique entries use `Key.encode(parts)` as their key. Nonunique entries use
`Key.encode(parts ++ [target])`; the `value` cell retains `Key.encode(parts)`.
Each indexed field combination has a fixed arity in the application's schema.
`lookup` reads `target`. `scan_equal` enumerates ALL index keys and reads BOTH
`target` and `value` of EVERY entry, then filters by equality. This is a useful
ordinary derived-table query. A faster nonunique lookup representation is deferred;
this scan is retained for explicit consistency/materialized-view examples.
Never grant index access if exposing its keys or filtered-out entries is forbidden.
`maintain` removes caller-supplied old keys, defines new entries, then executes
the supplied business action. `rebuild` enumerates all current keys, removes all,
and defines the supplied complete replacement entries. Both remain in the same
transaction. Correctness of the supplied base/index correspondence belongs to
the installed laws and application certificate, e.g. `TableLaws.ExactIndex`.
No helper auto-installs those laws or assumes the caller's rows are correct.

Summary tables have required columns `count: Integer`, `id: TextValue`,
`total: Integer`, keyed by `id`. `Summary.store` takes already obtained numeric
values, refuses on checked aggregation overflow, and emits one `DefineRow`.
Source reads and business writes must be composed by the application in the same
transaction. `ExactIndex` can also express an exact summary rebuild function.

`OnStable` explicitly permits transient invariant violations while executing and
requires the invariant in Stable and successful Closed phases. `OnEveryPrefix`
requires it in all phases. These are alternative administrator choices, not a
way for a client to weaken installed laws. Other laws still govern all actual
reads/writes at every prefix. Failed writes, refusal, limits and ordinary errors
retain the existing whole-call publication/rollback behavior.

### Numeric and algorithmic limits

All stored signed64 values remain two `U32` words, including INT64_MIN and
INT64_MAX; multiplication/division use bounded 64-step loops. Division truncates
toward zero; remainder has the dividend's sign. Checked arithmetic returns None
on overflow, division by zero, or INT64_MIN/-1. Aggregates use a right fold and
reject intermediate signed64 overflow even if a different summation order would
have a representable final sum. Average is an integer mean, not floating point.
Finite-list sizes/offsets are Nat; they are not conversions of stored integers.

Sorting is O(n²), grouping O(n × groups), joins O(left × right), and nonunique
index queries scan the complete index. Group items retain input order; group
order is descending order of last occurrence (sort first if another ordering is
needed). Pagination is offset/limit on each current obtained list. Separate
requests see successive current snapshots; no historical snapshot or stable
pagination across intervening writes is promised. Use an application-defined
sort key/order and accept current-snapshot semantics.

### Proofs and checks

Run heavy checks under the experiment lock:

```sh
flock /tmp/jaydb2-experiments-heavy.lock make test-library
```

The target checks the extension proof root with **both official checkers**, checks
an actual restricted-user application proof root, compiles unmodified official C
for a dynamic Python signed64 oracle, and runs the real task client against the
host. `make verify` also includes the extension root through `library/VERIFY`.
The real task flow adds `insert`, `replace_open`, `cas` and `drop` commands, and
proves all continuations including incorrect return variants. Negative mutated
programs attempt another user's reads before refusing or failing comparison;
the original certificates must be rejected. See the experiment report for the
actual commands/results and remaining formal proof scope.

General proofs include record/typed-integer roundtrips, key injectivity and the
public `Key.decode(Key.encode(parts))` roundtrip for every finite parts list,
two-sided checked add/sub overflow contracts, finite permission composition,
and take/drop boundaries. `SortProof.sort_content` preserves every predicate count and
`sort_occurrences` preserves each supplied value's multiplicity for arbitrary
lists/comparators. `Sorted` independently requires every earlier element to be
no greater than every later one; `sort_sorted` proves it under explicit
transitivity/totality obligations for the induced non-strict order.
`completed_sorted` discharges those obligations for the useful task order.
`ComparisonProofs.equal_sound` and `equal_complete` connect the actual structural
`Value.equal` Boolean to propositional equality for all values, including
malformed list/record tails. This supports exact comparisons in conditional
mutations and occurrence counts. Its signed-comparison theorems establish
irreflexivity, transitivity, asymmetry, equality reflection and trichotomy through
the actual sign-flipped word rank. They do not supply an independent mathematical
integer interpretation or arithmetic correctness theorem. The proof module is
optional; the runtime helpers retain their original dependency closures.
Concrete functional proofs also exercise grouping, joins, aggregate signs and
overflow, counter prefixes and index maintenance. A full algebraic proof of
signed multiplication/division is still outside the claimed scope.
Advanced ordered/range indexes remain later; full text, geospatial and a query
optimizer are excluded. Idempotency/receipt handling belongs to its own module
and is not duplicated here.

### Read-only construction subset

`ReadProgram.bend` targets the accepted `src/ReadOnly.bend` predicate without
changing the normal protocol. `cell(collection,key,column)` and
`select(collection,key,fields)` construct ordinary closed Actions; `program(fields)`
builds a small program whose text argument is a row key in the authenticated
context's named table. A selected record finishes; missing rows return VAbsent;
invalid fields or unexpected returns refuse. `cell` also returns VAbsent on
missing rows, so use the ordinary observation API if that distinction matters.

`cell_readonly`, `select_readonly` and `program_readonly` prove the finite
whole-continuation restriction, including every `Semantics.Return` variant.
`fields_readonly` requires the same restriction on the entire supplied
continuation. There is no recursive higher-order syntax to lower and no general
bind. An unreachable continuation containing a write is rejected by the negative
fixture `HiddenWrite.bend`. The ordinary administrator certificate is still
mandatory: the real restricted task test rejects an attempted Bob-table read
using this helper. Programs without this extra proof retain ordinary behavior;
this branch does not implement or claim host batching or prepared opcode 3.

The predicate file alone was imported from accepted concurrency commit
`b6ef4a6681906859fdcdd4caf5b85b8fd318dcd8`; its SHA-256 is
`e525c1eec917cca6e139f661c5aab9a9c64fd5375faea9fd980adb585632ed0a`.


### Audited sorting and certified index example

The additional focused native fixture `experiments/library/CollectionRuntime.bend`
accepts variable-length records with original identity payloads.
`test_collections.py` compares actual output contents against independent Python
references: stable sorting (numeric keys and completed-task keys), complete inner
and left join pairs, and every group key/member in order. Cases include empty,
singleton, reverse-sorted, mixed duplicates, forty equal keys, and random lengths
through 80. It does not use lengths/cardinalities as the functional oracle.

The [indexed availability application](../applications/indexed/README.md) is an
actual certified restricted-user business/index flow. Its administrator installs
`TableLaws.OnStable(ExactIndex)` alongside an every-prefix working-layout/access
law. `set` composes `Index.maintain` and the business write; `query` uses
`Index.scan_equal` to map an availability tag to matching targets; `rebuild`
reads business data and calls `Index.rebuild`. Its ordinary universal certificate
proves all transitions and the exact terminal projection through successful
publication. The example has one Boolean availability row per principal and two
fixed principals; arbitrary index-row lists are allowed only while executing.

Negative controls adapt each implementation's operation/layout proofs. Omitted
and forged maintenance independently pass ordinary permission proofs on all
valid states and all prefixes, then fail their full certificates at terminal
index-row equality. A forbidden index query fails at the first permission check.
The real host rejects all three and subsequent correct queries verify unchanged
state. No final-state runtime guard or assumed validity certificate is used.

Focused commands (run under the shared experiment lock):

```sh
python3 -B tools/check.py library/SortProof.bend
python3 -B experiments/library/test_collections.py
python3 -B applications/indexed/run_check.py
```

The report records the exact frozen source hashes, completed commands and logs.

## Index performance decision

Keep `Index.claim` and `Index.lookup` as optional unique-key helpers. The measured
benefit is workload-dependent: several uniqueness checks sharing a transaction
can avoid repeated business-table scans, while one lookup need not offset the
cost of carrying the extra index state. Maintaining an index also increases
write work. No universal lookup-speed improvement is promised.

The former `lookup_many` is now named `scan_equal`, without an old-name alias. It
is explicitly a full scan for ordinary derived tables, not an accelerated
nonunique lookup. The certified availability example retains this small utility
to demonstrate permissions and exact projection maintenance. A keyed
value-to-targets design is deferred; no new storage primitive or automatic
maintenance is added.

[Reproducible benchmark and measured evidence](../experiments/library/index_benchmark/README.md)
cover complete prepared requests, hits/misses, maintained updates, narrow/wide
rows, and batched unique checks. Historical measurements retain their original
revision and API spelling; they are not relabelled as new-source measurements.
## Optional receipt protocol

`Receipts.bend` provides exact canonical-input/operation-bound ordinary-table
lookup and small scalar writes. `ReceiptLaws.bend` provides prefix, completed
success and stable provenance law templates. They add no kernel privilege or
host retry machinery. See the [certified voucher flow](../applications/vouchers/README.md)
and [experiment report](../experiments/idempotency/REPORT.md) for contracts,
retirement semantics, proof scope and validation.

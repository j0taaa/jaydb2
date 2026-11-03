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

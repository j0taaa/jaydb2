# Certified row-level security on a shared notes table

Alice and Bob store notes in **one `notes` table** with required text columns
`id`, `owner`, and `text`. Public demonstration credentials are `alice-token`,
`bob-token`, and `admin-token`; authentication supplies the ID and role from
the current user registry. No caller-supplied owner or role is trusted.

Each ordinary user can read, test existence, replace, or delete only their own
rows. Even a foreign-row read followed by refusal violates the law. Full-row
insertion/replacement must supply the caller's owner. Ownership cannot change.
The explicitly authorized `admin` **role** can read any note, test existence,
enumerate all note keys, and count all notes. Admin has no exception for writes:
the write rule still requires its own key, so the seed's admin cannot write or
delete Alice/Bob notes. No role can read or mutate the registry through client
operations, or perform partial-column writes. The demo does not provision users,
change roles, transfer ownership, or confer any implicit kernel privilege.

## Unbounded-directory follow-up (incomplete)

The attempted follow-up is isolated in [`unbounded/`](unbounded/README.md).
It contains a bitmap-directory model, prototype CRUD/list actions, generic
key/directory algebra and concrete reference-interpreter examples beyond the
old cap. **It is not an admitted application: the universal mutation/publication
certificate is unfinished. The working app described below still has two slots.**

The [proof-gap report](unbounded/README.md#where-certification-remains-unfinished)
identifies the required actual-upsert/removal and publication obligations and
explains why ownership alone would be insufficient. No installed law, existing
negative control, host source or checker limit was weakened for this spike.
Its model controls must not be reported as new native admission-denial tests.

## Representation and listing

There are exactly two possible note slots per user: `alice/1`, `alice/2`,
`bob/1`, and `bob/2`. Each row redundantly stores its owner in the `owner`
column. `Policy.key_valid` defines the complete address space; `key_owner`
extracts the owner of those addresses. At every working prefix and publication,
every row must have a valid key, an owner field equal to that key's owner, and
a registered owner. Thus replacing or deleting/recreating a row at the same key
cannot transfer ownership. `Ownership.owner_immutable_at_key` proves this
relationship independently of any particular client.

The fixed slot bound makes proofs and private enumeration small and explicit.
`Client.list` tests existence of only the caller's two keys and returns the
present keys in order. It never invokes `EnumerateKeys` or observes another
user's existence. Listing covers all possible caller rows because the invariant
excludes every other key. The native engine may traverse its internal state to
resolve an addressed operation; internal representation work does not expose
those traversed rows to the program. This is a bounded notes demonstration,
not an arbitrary-prefix query primitive or an unbounded multi-tenant application.
The shared table has at most four rows, so the admin count fits the returned
integer representation.

## Installed administrator law

`Policy.Rule` is the single installed proposition. Its `Stable` case requires
`Owners(s)`; its `Executing` and `Closed` cases require both `Owners(w)` and
`AllAllowed(ctx, ts)`. The latter checks each actual operation, including failed
accesses and reads whose values the program discards. Representative definitions:

```bend
def WriteScope(id: String, +key: String) -> Data:
  Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>

# Allowed's full-row write case also requires the fixed owner field:
case D.DefineRow{D.Application{name}, +k, fs}:
  Both<{name == "notes" : String}, Both<WriteScope(id, k),
    {D.find_field(fs, "owner") == Some{D.VText{key_owner(k)}} : Maybe<&2, D.Value>}>>

# Reads explicitly distinguish the administrator role:
def ReadScope(admin: Bool, id: String, +key: String) -> Data:
  match admin:
    case True{}: Unit
    case False{}: Both<{key_owner(key) == id : String}, {key_valid(key) == True{} : Bool}>
```

`Allowed` passes `String.eq(kind, "admin")` to `ReadScope`, restricts the table
to `notes`, and requires `kind == "admin"` for whole-table enumeration/count.
Every other operation, including all registry and partial-column operations,
has the impossible obligation `False == True`.

These are proof obligations checked **before execution**, not runtime RLS
predicates. `Ownership.operation_preserves` reasons about actual `Data.operate`;
`Proofs.safe` covers every observation depth; `Proofs.finalize` proves validity
of the actual resulting state when technical publication checks succeed.
`ClientProof.certify` quantifies over every valid initial state and authenticated
context, not only this seed. Termination covers arbitrary states and returns,
with an action-depth witness of three (two operations plus a terminal action).
It is not a host timeout. No law or checker fuel limit is weakened.

## PostgreSQL comparison

The PostgreSQL column describes its RLS policy mechanism, rather than all
features that can be built with SQL constraints, triggers, and functions.

| Concern | PostgreSQL RLS | This JayDB2 application |
| --- | --- | --- |
| Reading foreign rows | `USING` filters rows during query execution. | An attempted foreign observation prevents certificate admission. |
| Insert/new update values | Runtime `WITH CHECK`; a violating command errors. | The certificate must prove the new owner matches caller and key. |
| Existing update/delete targets | `USING` limits candidate rows. | Every addressed write/delete requires caller ownership before execution. |
| Administrator reads | Policies can grant reads; superusers/`BYPASSRLS` bypass RLS, and table owners normally bypass it. | Only the explicit role branch in the installed law grants wider reads. |
| Policy scope | Row visibility/new-row Boolean predicates, with expressions able to consult other data. | Propositions over stable state, every execution prefix, operations and outcome; this example uses ownership, registry membership and access traces. |
| Whole-table listing | Query returns rows remaining after filtering. | Ordinary listing probes two authorized slots; an ordinary global scan is uncertifiable. |
| Publication | RLS applies while executing statements. | Admission proves prefix obligations and final published-state validity; the native host publishes only complete success. |

PostgreSQL references: [row security policies](https://www.postgresql.org/docs/17/ddl-rowsecurity.html)
and [CREATE POLICY](https://www.postgresql.org/docs/current/sql-createpolicy.html).
In particular, filtering applies to `USING`; `WITH CHECK` violations are errors,
so it would be inaccurate to describe all PostgreSQL RLS checks as silent.
JayDB's broader proposition interface does not imply automatic proof discovery.
Its existing [T1–T3 assumptions](../../proof/README.md) still apply, including
compiler/runtime preservation and native host plumbing. Physical timing and
resource-consumption channels remain outside the confidentiality guarantee.

## Commands and proof files

Arguments are ordinary canonical values (shown below as JSON arrays).
The Boolean slot selector is `false` for `/1` and `true` for `/2`.

| Caller | Arguments | Successful value |
| --- | --- | --- |
| Alice/Bob | `["save", false, "text"]` | Own key; inserts or replaces the complete row. |
| Alice/Bob | `["view", false]` | `{id, owner, text}`, or absence for a missing own note. |
| Alice/Bob | `["remove", false]` | Own key; removing an absent row also succeeds. |
| Alice/Bob | `["list"]` | All present own keys. |
| Alice/Bob | `["cancel", false, "discard"]` | Refusal `"cancelled"` after a provisional write; nothing publishes. |
| Admin | `["read", "bob/1"]` | `{id, owner, text}`, or absence for a missing note. |
| Admin | `["count"]` | Number of rows in the shared table. |

An unsupported command is a runtime `refusal` from the certified dispatcher.
That is distinct from a submitted program which actually attempts a forbidden
operation: the latter must fail admission with status `certificate`.

| File | Responsibility |
| --- | --- |
| `Configuration.bend`, `Policy.bend`, `Seed.bend` | Shared schema, administrator law, registered users and initial-validity proof. |
| `Client.bend` | Executable commands, private listing, explicit admin reads/count. |
| `ClientProof.bend` | Local permissions, certificate and termination bindings. |
| `Ownership.bend` | Preservation by real row writes/removals and same-key owner immutability. |
| `Proofs.bend` | Prefix induction and technical finalization/publication composition. |
| `check.py`, `negative_cases.py`, `test.py` | Public namespace packaging, both official checkers, causal negatives and real native session. |

The prefix infrastructure is adapted from tasks. `Ownership` changes the new-row
witness to the shared-table key/owner invariant; the other row-list preservation
lemmas retain their generic structure. Existing library `Laws`/`Query`/`Action`
and `proof/Orders`/`Foundations` are packaged unchanged apart from relocated
imports. Generated offline `Instance`/`Bindings` modules bind the exact code
literal and actual certificate targets; host admission uses the original full
sources with its own frozen environment, without private data in proof files.

## Run checks and native tests

Run from the repository root with the pinned tools installed:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B applications/rls/check.py --proof-only'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make test-rls'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make verify'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make test'
```

`make verify` includes this application's proof checks. `make test` includes
`test-rls`. The targets rely on the caller holding the lock; they acquire no
nested lock. `check.py` defaults to both proof modes plus the real native session;
`test.py` runs only the native session. Generated sources and diagnostic logs
remain in ignored `applications/rls/.build/`.

The positive session checks ordinary admission/execution, Alice/Bob creation,
reads, updates, deletion, absent reads, one/two/zero-result private listings,
admin reads of both owners and whole-table counts, write-then-refuse rollback,
authentication, universal preparation, cross-user handle reuse and invalidation.
The prepared proof is derived from the same parameterized certificate, with
fresh authentication and current state on every use.

Five independent negative programs use filled certificates adapted to their
actual operations. In both official modes **only `false` may fail**, with
expected/observed diagnostics; any missing import, open definition, helper
co-failure, or unrelated parse error fails the harness:

| Negative program submitted as Alice | Intended failing obligation |
| --- | --- |
| Read `bob/1`, then refuse | `ReadScope`: `bob == alice`. |
| Replace existing `bob/1` | `WriteScope`: `bob == alice`. |
| Insert fresh `alice/2` with owner Bob | Owner field must be Alice, as required by key/caller. |
| Replace existing `alice/1` with owner Bob | The same owner-field obligation prevents ownership transfer. |
| Enumerate all note keys, even discarding the result | Whole-table enumeration requires role `admin`, not `user`. |

The real host must refuse each at `PRIMARY_CHECK`/`false`. After each denial,
the same prepared artifact verifies both private listings, total count, and the
complete row/absence of **every possible key**. Valid state fixes every owner field
to its prefix, and the registry cannot be changed by these operations. Thus the
checks cover the complete application state, not only the denied operation's
response.

## Line-count definition

Counts are nonblank physical Bend lines, including comments and imports, using
`sum(bool(line.strip()) for line in path.read_text().splitlines())`, as in
[the paper's size definitions](../../paper/README.md). Scoped client integration
counts exclude schema/model/seed/policy and ownership infrastructure, like the
paper's client comparison. A separate total discloses all locally maintained
proof infrastructure, including the adapted ownership proof; no claim that it
is free is intended.

| Scope | Files | Nonblank lines |
| --- | --- | ---: |
| Client program | `Client.bend` | 91 |
| Scoped client certificate | `ClientProof.bend` | 112 |
| Ownership/prefix infrastructure | `Ownership.bend`, `Proofs.bend` | 370 |
| All admitted application-local proof files | All three files above | 482 |

Scoped proof/program ratio: **1.23**. Including all local proof infrastructure: **5.30**.

## Follow-up model line counts

The isolated, uncertified prototype uses the same nonblank physical-line
counter. Its files are excluded from the admitted-app totals above.

| Follow-up scope | Files | Nonblank lines |
| --- | --- | ---: |
| Prototype program | `unbounded/Client.bend` | 127 |
| Generic representation/key algebra | `unbounded/DirectoryProof.bend` | 91 |
| Concrete model/interpreter examples | `unbounded/Examples.bend` | 63 |
| Model and proposed invariant | `unbounded/Model.bend` | 70 |
| Completed unbounded client certificate | None | **Not implemented** |

There is no meaningful unbounded certificate/program ratio: the missing
certificate must not be counted as zero proof cost. The working app's **1.23**
scoped and **5.30** all-local ratios remain unchanged.

## Follow-up validation result — incomplete feature

Validated on 2026-11-11 from `fa819db`. `make build` passed first. All heavy
commands ran with the common lock held and unlimited stack; no checker fuel or
configured state limit changed. The original app remains the certified two-slot
version. The following passing regressions **do not certify the unbounded
prototype**.

| Command | Result and scope |
| --- | --- |
| `python3 -B applications/rls/unbounded/check_model.py` | Passed both official modes for generic model/key algebra and the concrete reference-interpreter examples. All four model controls failed only at `false` in both modes with expected/observed directory text. |
| `python3 -B applications/rls/check.py --proof-only` | Passed the original ordinary/universal certificates, termination, seed and five causal negatives in both modes. |
| `make test-rls` | Passed the original 81-response native session, including all five admission denials and unchanged-state checks. |
| `make verify` | Passed import coverage, all three existing positive roots in both modes, 373 negative fixtures / 746 official-mode rejections, and the original RLS proof gate. |
| `make test` | Passed admission/verifier, 10 native runtime, 36 Rust host and 16 service integration tests, followed by another successful original 81-response RLS session. |

Logs are in `.build/unbounded-validation/`; model-control diagnostics are
`.build/unbounded-*-check-only.log` and `.build/unbounded-*-verdict.log`.
The full unbounded client certificate, new native CRUD/admission tests and
unbounded prepared reuse remain unfinished. The proposed exact directory law
has not been installed, and no ownership-only alternative was substituted.

## First-version validation result

Validated on 2026-11-11 from base `ff96188` with the pinned official toolchain.
`make build` ran first. All heavy commands used the shared lock and unlimited
stack shown above. The native toolchain sources and BendTT artifact were
bootstrapped from existing local copies with the standard hash-checking installer.

- `check.py --proof-only`: complete ordinary and universal certificates,
  termination and seed validity passed both official modes. Each of the five
  filled false certificates failed only at `false` in both modes.
- `make test-rls`: passed, with 81 checked native responses plus the checked
  preparation receipt. All five attacks were rejected at admission and every
  row/absent slot was checked unchanged after each denial.
- `make verify`: passed all three existing positive roots in both modes,
  import coverage, 373 existing negative fixtures (746 official-mode
  rejections), and the newly wired RLS proof checks.
- `make test`: passed 30 admission/verifier tests, 10 native runtime tests,
  36 Rust host tests, 16 service integration tests, and the complete RLS gate
  again (another successful 81-response native session).

No application law was weakened to obtain these results. Generated proof
roots, intended-failure diagnostics, the native host log, and the complete
validation output remain under `.build/` for local inspection.

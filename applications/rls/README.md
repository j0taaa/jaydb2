# Certified row-level security with unbounded per-user notes

Alice and Bob store notes in **one shared `notes` table** (`id`, `owner`,
`text`). Each user also has a private **directory table** (`alice_dir`,
`bob_dir`, columns `id`, `owner`) whose rows are exactly the ids of that user's
notes. Public demonstration credentials are `alice-token`, `bob-token` and
`admin-token`; authentication supplies the id and role from the current user
registry. No caller-supplied owner or role is trusted.

There is no slot count. Users share one configured 65,536-byte state limit;
the earlier two-slot version is replaced. This shared capacity reveals aggregate
size information and permits cross-user denial of creation (see "Limits and
assumptions").

## Representation

| Table | Key | Meaning |
| --- | --- | --- |
| `notes` | `alice/00000001`, `bob/00000007`, ... | Shared business rows; the key prefix names the owner and the `owner` column repeats it. |
| `alice_dir`, `bob_dir` | the note id | One row per note the user owns. |

Ids are fixed-width decimals under the owner's prefix, so their string order
is numeric. `create` enumerates only the caller's own directory, takes the
largest id and adds one. Deleting the largest id and creating again reuses it
(the id is fresh with respect to the current notes, which is all the laws need).
Deletion removes both rows; nothing is kept as a tombstone.
A previously returned id can later name different content, so saved references
can become stale.

Listing uses the caller's rows: a user enumerates **only their own directory
table** and then reads each listed note. No user operation enumerates or counts
the shared table, and no user operation tests whether another user's row exists.

## Installed administrator laws

`Policy.laws()` installs two propositions. Both are checked before execution;
neither is a runtime predicate.

**`Rule` — every working prefix, every closed result.** The existing RLS law,
generalized from four fixed keys to every key in the two namespaces:

```bend
def key_owner(+k: String) -> String:
  Bool.pick(String, starts("alice/", k), "alice", Bool.pick(String, starts("bob/", k), "bob", ""))

# Every row of every table carries its key's owner, who must be registered.
def Owner(+us: List<&2, D.Row>, name: String, +l: D.Row) -> Data:
  Both<{key_valid(D.row_key(l)) == True{} : Bool},
    Both<{D.find_field(fields(l), "owner") == Some{D.VText{key_owner(D.row_key(l))}} : Maybe<&2, D.Value>},
      {D.exists_row(D.find_row(us, key_owner(D.row_key(l)))) == True{} : Bool}>>

case D.DefineRow{D.Application{+name}, +k, fs}:
  Both<Writable(id, name), Both<WriteScope(id, k),
    {D.find_field(fs, "owner") == Some{D.VText{key_owner(k)}} : Maybe<&2, D.Value>}>>
case D.EnumerateKeys{D.Application{name}}:
  KeysScope(String.eq(kind, "admin"), id, name)   # a user: only name == id ++ "_dir"
```

In words: users read, test, write and delete only rows whose key is in their
own namespace (`ReadScope`/`WriteScope`), even if they later refuse; inserted
or replaced rows carry the caller as owner, so ownership never changes at a key;
writes reach only `notes` and the caller's own directory (`Writable`); a user
enumerates only their own directory. The `admin` **role** may read any note,
count notes and enumerate keys of `notes`, `alice_dir` and `bob_dir`, but has no
write exception. Every other operation, including all registry and
partial-column operations, has the impossible obligation `False == True`.

**`DirectoryRule` — exact directory at stable states.**

```bend
def listed(rows: List<&2, D.Row>, +k: String) -> Bool:
  D.exists_row(D.find_row(rows, k))

def owned(+p: String, rows: List<&2, D.Row>, +k: String) -> Bool:
  row_owner(D.find_row(rows, k), p)       # the note at k has owner column p

def Agree(+p: String, +ds: List<&2, D.Row>, +ns: List<&2, D.Row>) -> Type:
  @k: String -> {listed(ds, k) == owned(p, ns, k) : Bool}

def Directory(+s: D.State) -> Type:
  L.E<Agree("alice", rows(dir_name("alice"), s), rows("notes", s)),
    Agree("bob", rows(dir_name("bob"), s), rows("notes", s))>
```

In words: for **every** string `k`, `k` is in Alice's directory exactly when
the shared table holds a note at `k` whose `owner` column is `alice` (and
likewise for Bob). The contract's structural validity makes keys strictly
ordered, so neither list has duplicates: each directory lists exactly the ids of
the notes its user owns, no more and no fewer.

The law is stated for `Stable` situations. A success-`S.Closed` obligation
occurs only inside [`Requirements.SafetyFinal`](../../contract/Requirements.bend),
paired with `PublicationValid(finalize(r, c, w), c, w)` by `SafetyTrace`.
When the finalized response succeeds, this is `Valid(c, w)`, which includes
every stable law. (`SafetyPrefix` also checks `S.Closed`, but only with a
`Failure` response.) In addition,
[`Theorems.Completion`](../../contract/Theorems.bend) gives `Valid(c, next)`
for the published state. Thus every published root satisfies the directory
equality, and a separate success-`Closed` clause would repeat the publication
obligation. Working prefixes may be stale (after the note write and before the
directory write), exactly as in `applications/indexed`.

## How the certificate works

`Proofs.Safe(d, e, ctx, s, a)` is a weakest precondition over the **real**
`Data.operate` result. Each access needs its `Allowed` permission and a proof
for the actual result: data failure (nothing to prove), an observation at the
same state, or a change to the actual new state. `Finish` needs
`Directory(working)`; `Refuse` needs nothing because nothing publishes. The
depth `d` only bounds unfolding; `Proofs.safe` uses it at depth `n + 1` for
observation depth `n`, so every trace prefix and every final outcome is covered.
The every-prefix ownership law is preserved separately by
`Ownership.operation_preserves`, unchanged from the two-slot version.

`Directory.bend` proves the transitions on arbitrary row lists, with no
sortedness or uniqueness assumption, using the unchanged library lemmas for
`insert_row`, `remove_row` and table swaps:

| Lemma | Statement (informally) |
| --- | --- |
| `save_same` | Upserting note `id` (owner `p`) and directory entry `id` preserves `Agree(p, ...)`. |
| `remove_same` | Removing `id` from both preserves `Agree(p, ...)`. |
| `save_other`, `remove_other` | The other user's agreement survives, because the every-prefix law makes a note at `p/...` owned by `p` (`not_owned`). |
| `pair` | The actual two-step state (note table swapped, then `p`'s directory swapped) has exactly those row views; the other directory is untouched. |

`ClientProof.bend` quantifies over every valid initial state, authenticated
context, argument and observation depth. The prepared (universal) form is the
same proof with the context and arguments abstracted. Termination
(`Completion.bend`) holds on arbitrary, even invalid, states: listing's bound
is the actual number of directory keys observed plus one; every other command
is bounded by four steps.

## Commands

Arguments are canonical values, shown as JSON arrays.

| Caller | Arguments | Successful value |
| --- | --- | --- |
| Alice/Bob | `["create", "text"]` | New id, e.g. `"alice/00000007"`; writes the note and its directory entry. |
| Alice/Bob | `["list"]` | `[{id, text}, ...]` for every id in the caller's directory, in id order. |
| Alice/Bob | `["view", "alice/00000003"]` | `{id, text}`, or absence for a missing own id. |
| Alice/Bob | `["update", "alice/00000003", "text"]` | The id; refuses `"no such own note"` if it does not exist. |
| Alice/Bob | `["remove", "alice/00000003"]` | The id; removes the note and its directory entry. |
| Alice/Bob | `["cancel", "text"]` | Refusal `"cancelled"` after a provisional create; nothing publishes. |
| Admin | `["read", "bob/00000001"]` | `{id, text}`, or absence. |
| Admin | `["count"]` | Number of rows in `notes`. |

A user id outside the caller's namespace is refused (`"no such own note"`)
before any access; unsupported commands refuse with `"unsupported"`. These are
runtime refusals of the certified dispatcher. A submitted program that actually
attempts a forbidden operation fails admission with status `certificate`.

## PostgreSQL comparison

The PostgreSQL column describes its RLS policy mechanism, not everything that
can be built with constraints, triggers and functions.

| Concern | PostgreSQL RLS | This JayDB2 application |
| --- | --- | --- |
| Reading foreign rows | `USING` filters rows during query execution. | An attempted foreign observation prevents certificate admission. |
| Insert/new update values | Runtime `WITH CHECK`; a violating command errors. | The certificate proves the new owner matches caller and key. |
| Existing update/delete targets | `USING` limits candidate rows. | Every addressed write/delete requires caller ownership before execution. |
| Administrator reads | Policies can grant reads; superusers/`BYPASSRLS` bypass RLS, and table owners normally bypass it. | Only the explicit role branch grants wider reads; no write exception. |
| Listing own rows | A filtered scan of the shared table. | The user scans only their own directory table; a scan of the shared table is uncertifiable for users. |
| Directory = owned notes | Not an RLS property; it needs triggers or deferred constraints that run at execution/commit time. | A stable-state law proved for every transaction **before** it runs; a program that forgets the directory write is not admitted. |
| Publication | RLS applies while executing statements. | Prefix obligations plus validity of the published state, including the directory law; the host publishes only complete success. |

PostgreSQL references: [row security policies](https://www.postgresql.org/docs/17/ddl-rowsecurity.html)
and [CREATE POLICY](https://www.postgresql.org/docs/current/sql-createpolicy.html).
JayDB's broader proposition interface does not imply automatic proof discovery.
Its existing [T1–T3 assumptions](../../proof/README.md) still apply, including
compiler/runtime preservation and native host plumbing. Physical timing and
resource-consumption channels remain outside the confidentiality guarantee.

## Files

| File | Responsibility |
| --- | --- |
| `Configuration.bend`, `Policy.bend`, `Seed.bend` | Schema, the two installed laws, registered users, initial-validity proof. |
| `Client.bend` | Executable commands. |
| `ClientProof.bend` | Per-command certificates, termination and the bindings. |
| `Proofs.bend` | State-indexed judgment, prefix induction and publication. |
| `Directory.bend` | Directory transitions over actual row operations and table swaps. |
| `Ownership.bend` | Every-prefix ownership preservation (unchanged). |
| `Completion.bend` | Observation-dependent termination witnesses (from `applications/indexed`). |
| `check.py`, `negative_cases.py`, `test.py` | Packaging, both official checkers, negatives and the native session. |

`Configuration.bend` imports `Proofs`, `Directory` and `Completion`: the host
publishes exactly the administrator's import closure as modules a client
certificate may import, so these proof helpers are part of the installed
configuration (as `Proofs` already was in the two-slot version).

`check.py` packages unchanged library lemmas (`RowLookupProofs`,
`RowRemovalLookupProofs`, `CollectionFrameProofs`, `MutationStateShapeProofs`,
`ValueScalarProofs`, `Value`, `ReadOperationProofs`) and `proof/Orders`,
`proof/Foundations` with relocated imports only. Its offline `Bindings` module
writes the client source as a `++` chain of literal chunks that joins to the
exact source (asserted): the pinned native translator for `--verdict` overflows
its stack expanding a single literal longer than about 5,000 characters. The
real host binds its own exact literal.

## Run checks and native tests

From the repository root with the pinned tools installed:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B applications/rls/check.py'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make test-rls'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make verify'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make test'
```

`make verify` includes this application's proof checks; `make test` includes
`test-rls`. The targets acquire no nested lock. `check.py` defaults to both
proof modes plus the real native session; `test.py` runs only the native
session. Generated roots and logs stay in ignored `applications/rls/.build/`.

## Negative fixtures

Each fixture is a complete certificate for its actual one-operation program,
built from the same `Proofs`/`Directory` machinery; only `false` is wrong. In
both official modes **only `false` may fail**, with expected/observed
diagnostics; any missing import, open definition, helper co-failure, linearity
error or stack overflow fails the harness. Fixtures are submitted as Alice
except the administrator-write fixture, whose offline and native contexts are
both the authenticated `admin` id and role.

| Negative program | Intended failing obligation (observed vs required) |
| --- | --- |
| Read `bob/00000001`, then refuse | `ReadScope`: `"bob" == "alice"`. |
| Test existence of `bob/00000001`, then refuse | `ReadScope`: `"bob" == "alice"`. |
| Count rows of `notes`, then refuse | Admin role required: `"user" == "admin"`. |
| Admin replaces `alice/00000001`, then refuses | `WriteScope`: `"alice" == "admin"`; there is no admin write exception. |
| Replace existing `bob/00000001` | `WriteScope`: `"bob" == "alice"`. |
| Insert fresh `alice/00000099` with owner Bob | Owner field must be `D.VText{"alice"}`. |
| Replace existing `alice/00000001` with owner Bob | The same owner-field obligation (no ownership transfer). |
| Enumerate the shared `notes` table | `KeysScope`: `"notes" == "alice_dir"`. |
| Enumerate Bob's directory | `KeysScope`: `"bob_dir" == "alice_dir"`. |
| Add foreign id `bob/00000001` to Alice's directory | `WriteScope`: `"bob" == "alice"`. |
| Create `alice/00000099` without a directory entry | `Agree("alice", ds, insert_row(ns, note))` from `Agree("alice", ds, ns)`. |
| Remove `alice/00000001` from the directory, keep the note | `Agree("alice", remove_row(ds, id), ns)` from `Agree("alice", ds, ns)`. |

The last two `false` laws are genuinely false: the empty seed, respectively a
state with one listed note, is a counterexample at the written key. The
permission negatives end in `Refuse`, so the permission is their only
obligation. The directory negatives end in `Finish`; their permission, the
other user's agreement and all frame equalities are proved, and only Alice's
directory law fails.

## Native session

`test.py` drives the real host through the framed ordinary and prepared APIs.
Alice creates a note with an ordinary certificate; a universal (prepared)
certificate is then admitted once and reused, with fresh authentication and
current state, for every later call by Alice, Bob and the administrator. Alice
creates seven notes (six present at once), Bob three (two present at once);
listings, views, an update, deletions, a create after deletions, admin reads and
counts are checked exactly. Bob deletes his largest id and creates again;
the returned id is the same, and viewing it returns the replacement content.
Runtime refusals cover foreign ids, a deleted id, cancel-after-write rollback and unsupported
commands. Each of the twelve negatives is refused at admission (`PRIMARY_CHECK`,
`Location: false`), and after each the same prepared artifact checks both
listings, the count and the presence or absence of eleven possible keys.
Finally Alice removes all notes, an invalid token is refused and the handle is
invalidated.

## Limits and assumptions

- The principals are fixed at configuration time (one directory table and one
  key namespace each), as the two-slot version fixed them; the number of notes
  is bounded only by the shared 65,536-byte state limit.
- This single state-size limit is an **aggregate-size channel** and a
  **cross-user availability limit**. A user can choose note lengths and
  binary-search the deterministic `limit` status to learn the combined encoded
  size of other users' notes and directory entries. A user can also fill the
  shared state so others cannot create notes; capacity is not isolated per user.
  This logical response channel is outside the confidentiality claim, even
  though it is deterministic and is not a physical timing channel.
- Ids are eight decimal digits. Deleting the largest id and creating again
  reuses it. Past `99999999` the carry leaves the namespace and `create`
  refuses; the state limit makes that unreachable.
- `list` and `create` check the namespace of each id they derive from the
  directory at runtime. At valid states the check always passes (the directory
  law and the ownership law put only own ids there); it exists because the
  certificate does not inspect observed values.
- `view`, `list` and admin `read` return `{id, text}`; the owner is the id's
  namespace, which the ownership law ties to the `owner` column.
- The administrator may enumerate keys of the notes table and both directories;
  directories hold only note ids, which the administrator can already read.

## Line counts

Counts are nonblank physical Bend lines, including comments and imports, using
`sum(bool(line.strip()) for line in path.read_text().splitlines())`, as in
[the paper's size definitions](../../paper/README.md).

| Scope | Files | Nonblank lines |
| --- | --- | ---: |
| Client program | `Client.bend` | 126 |
| Client certificate (incl. termination) | `ClientProof.bend` | 320 |
| Judgment and publication | `Proofs.bend` | 175 |
| Directory transitions | `Directory.bend` | 190 |
| Ownership preservation (unchanged) | `Ownership.bend` | 259 |
| Termination witnesses | `Completion.bend` | 35 |
| All application-local proof files | the five files above | 979 |
| Schema, laws, seed | `Configuration.bend`, `Policy.bend`, `Seed.bend` | 163 |

Certificate/program ratio: **2.54**. All local proof files/program: **7.77**.
The two-slot version had 91 program lines, 112 certificate lines (1.23) and 482
local proof lines (5.30).

## Validation result

Validated on 2026-11-11 with the pinned official toolchain (BendTT and native
sources reused through a temporary `.tools` symlink to the existing local
toolchain). All heavy commands ran under the shared lock with unlimited stack:
`make build`, `python3 -B applications/rls/check.py` (full default),
`make test-rls`, `make verify`, `make test`. No checker fuel, state limit,
contract, host or library file changed.

| Command | Result |
| --- | --- |
| `make build` | Passed. |
| `python3 -B applications/rls/check.py` | Positive certificate/termination/seed and the universal certificate passed both official modes; all twelve negatives failed only at `false` in both modes; native session passed with 253 checked responses and twelve admission denials, each followed by a complete unchanged-state check, plus largest-id deletion/reuse with replacement content. |
| `make test-rls` | The same full RLS gate passed, including all twelve negatives in both modes and the 253-response native session. |
| `make verify` | Import coverage and the existing positive roots passed in both modes; 373 negative fixtures / 746 official-mode rejections; this application's proof gate (as above, without the native session) passed. |
| `make test` | 30 admission/verifier tests, 10 native runtime tests, 36 Rust host tests and 16 service integration tests passed, followed by another passing RLS gate (253-response native session). |

Generated roots, intended-failure diagnostics and the host log stay under the
ignored `applications/rls/.build/`.

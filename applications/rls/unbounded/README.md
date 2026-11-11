# Unbounded-directory proof spike — incomplete

This directory is **not an admitted replacement for the RLS application**. The
working application one directory above remains the certified two-slot version
at `fa819db`. Its policy, client certificate, seed and Makefile wiring are
unchanged. This spike records an attempted representation and the exact proof
gap; it must not be described as removing the production note cap.

## Representation

Alice and Bob would keep `alice/_dir` and `bob/_dir` in the same shared `notes`
table as the business rows. The existing `id`, `owner`, `text` schema suffices:
the directory's `text` is a bitmap, with `+` for a present note and `-` for a
permanently reserved, deleted position. New allocations prepend `+`. There is
no fixed slot count and no integer conversion. The finite 65,536-byte state
limit still applies; this is not infinite storage.

Addresses are `alice/z`, `alice/az`, `alice/aaz`, and so on. The position's
address depends on the length of the bitmap suffix to its right. Prepending a
new position and replacing a character with `-` therefore preserve all existing
ids. Tombstones are retained, so allocation never reuses a deleted address.
This costs history space and gives quadratic total key bytes as note count
grows; compaction or a denser encoding would be separate work.

`Client.bend` is an executable **prototype without a client certificate**:

| Request | Draft behavior |
| --- | --- |
| `["create", "text"]` | Read own directory, allocate a fresh id, write the note and directory. |
| `["list"]` | Read own directory, then owner/text of each active own note; return note records. |
| `["view", "alice/z"]` | Consult own directory before reading an active note. |
| `["update", "alice/z", "replacement"]` | Require own directory membership and replace the note. |
| `["remove", "alice/z"]` | Require own directory membership, remove the row, write the tombstone. |
| `["cancel", "text"]` | Perform provisional creation and propose refusal. |
| `["read", "bob/z"]`, `["count"]` as admin | Read any addressed row or count all physical rows, including the two directories. |

The draft neither enumerates global keys nor tests foreign row existence.
Those facts about its source are **not** an admission or confidentiality proof.

## Proposed exact publication law

`Model.parts(a,b,da,db)` allows arbitrary directory text at intermediate prefixes.
`Model.state(a,b)` fixes it to the exact bitmap of the arbitrary finite slot
histories `a` and `b`. `Some{text}` generates precisely one physical note at its
position's address; `None` generates none. No other business rows are present.
The proposed stable-state proposition is:

```bend
type ExactProof<-s: D.State> is Data:
  Exact{a: List<&2, Maybe<&2, String>>, b: List<&2, Maybe<&2, String>>,
    same: {s == state(a, b) : D.State}}

def Coherent(s: D.State) -> Data:
  ExactProof<s>
```

This would be installed with `TableLaws.OnStable(~Model.Coherent, situation)`,
alongside the existing every-prefix ownership/access law. It is **not installed**
in the working configuration. Like the indexed application, it deliberately
allows stale directories between the note write and directory write. The old
four-address `key_valid`/`key_owner` cases would also need a checked namespace
extension covering both directories and arbitrary generated note addresses;
the current installed policy rejects the new addresses.

The candidate model fixes the registry to the three demo users. That is a
stronger layout restriction than the original ownership invariant, not a theorem
derived from the original `Valid` premise. A production implementation must
explicitly install that stronger invariant or factor the unchanged registry out
of the model; it cannot reuse the old validity premise as if it supplied this
new canonical-state witness.

`DirectoryProof.exact_directory_keys` connects the representation to literal
row keys for arbitrary histories, rather than only the six-note example:

```bend
{active_keys(p, M.mask(xs)) ==
  D.keys_rows(M.notes(p, xs, Nil{})) : List<&2, String>}
```

`fresh_before_notes` establishes that a newly allocated key sorts before every
existing generated note key. `insert_first` is a generic lemma about the real
`Data.insert_row`. Together with stable structural validity, exact key equality
would exclude missing/extra/duplicate directory entries. Duplicate ids and
foreign namespaces cannot be expressed by a valid bitmap position. Writing
foreign id text into a directory violates its required exact bitmap text.

## Where certification remains unfinished

The missing theorem is the universal **operation-to-publication** proof. Given
arbitrary histories, a valid initial state and authenticated context, it must
cover every actual `Data.operate` result and every observation depth, then
produce `Model.Coherent(working)` whenever a success survives finalization.

In particular, creation needs to lift the key-order lemmas through the shared
table's preceding directory row and the other owner's suffix. Its generic
business-row equality has the following form (all names are actual model
functions):

```bend
D.insert_row(
  M.dir(M.Alice{}, da) <>
    M.notes(M.Alice{}, a, M.dir(M.Bob{}, db) <> M.notes(M.Bob{}, b, Nil{})),
  M.row(M.Alice{}, a, text))
==
M.dir(M.Alice{}, da) <>
  M.notes(M.Alice{}, Some{text} <> a,
    M.dir(M.Bob{}, db) <> M.notes(M.Bob{}, b, Nil{}))
```

That must then be composed with schema/address validation, the actual directory
replacement and `Requirements.SafetyTrace`. Arbitrary-id updates/removals also
need a length-preserving edit lemma, a proof that its interpreted business rows
are exactly the actual upsert/removal result, and the corresponding bitmap
identity. Those universal transition/composition obligations were not completed.
The concrete interpreter examples do not discharge them. The existing
`Proofs.Safe` is a permission-only judgment and does not establish final directory
coherence; the candidate needs a state-indexed judgment over the real operation
result, as in `applications/indexed/CheckedActions.bend`.

The original `B.terminates` also has a constant three-action-depth witness.
Unbounded listing requires an actual-directory-length-dependent witness for
arbitrary states and returns, including malformed directory text. Structural
recursion in the draft source is not itself a proof of the service's
`ProgramTerminates` target. Neither new binding was completed, so no ordinary
or universal/prepared certificate is supplied. No checker incompleteness or
impossibility result has been established.

An ownership-only prefix law is a weaker, honest alternative: it can forbid
foreign accesses and owner changes while allowing a note write that omits its
directory update. That law permits permanently stale directories and incomplete
listing. It does **not** meet the requested goal and has not replaced the
working application's policy.

PostgreSQL RLS likewise does not itself establish this cross-row exact
maintenance property; transaction/constraint/trigger logic is a separate concern
from the RLS policies compared in the parent README. The intended JayDB2
advantage here would be a proof of that publication property. This spike does
not yet deliver that proof. The existing T1–T3 assumptions in `proof/README.md`
would still apply after certificate completion.

## Checks and boundaries

From the repository root, after `make build`, run:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; python3 -B applications/rls/unbounded/check_model.py'
```

The positive root checks the generic directory/key-order lemmas and a six-note
representation. Concrete reference-interpreter proofs execute the sixth create
from a five-note model state, two deletions and listing every survivor's payload.
Other checks cover stable survivor ids, the next fresh id and a six-note state
fitting the existing state limit. These bypass admission and are **not native-host
tests** or a sequential six-create native session.

Four filled false model equalities exercise actual `Data.operate`: missing
directory maintenance after insertion, removing a directory entry without
removing its note, writing a foreign id into the directory, and adding an extra
active position. The harness requires failure only at `false`, with the expected
and observed directory text in both official modes. These are model controls,
**not complete client-certificate negatives or admission-denial tests**.

The production app's existing native tests still cover its old five attacks,
rollback and prepared reuse. Unbounded native CRUD, unbounded prepared reuse,
the requested new admission negatives, and their unchanged-state checks remain
unimplemented because the full client certificate is missing.

Validation results and nonblank line counts are recorded in the parent README.

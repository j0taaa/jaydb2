# Certified per-user availability index

A small actual application of the ordinary library. Alice and Bob each own one
availability record (`item`) and a separate ordinary secondary-index table.
`alice` / `bob` have columns `available: Boolean, id: TextValue`;
`alice_index` / `bob_index` have `id, target, value: TextValue`.
The projection maps each business row to `Index.entry(key, [tag(available)], key)`;
tags are `ready` and `busy`. There is no special index primitive.

Requests use the normal framed code/proof protocol and ordinary credentials:

- `["set", true]` or `["set", false]`: `Index.maintain` removes the old index
  entry, writes its exact replacement, then writes the business availability.
- `["query", true]` or `["query", false]`: `Index.lookup_many` enumerates index
  keys, reads every entry's target/value, and returns matching targets. The
  result is `["item"]` or `[]`; even nonmatching reads require permission.
- `["rebuild"]`: reads the business availability, then uses `Index.rebuild` to
  enumerate, remove and reconstruct the index from that actual business value.

The administrator installs TWO independent laws. `Policy.Rule` requires the
fixed business/user layout at every prefix and proves each actual access is in
the authenticated principal's business table or index table. It deliberately
allows arbitrary index-row lists during execution. `Policy.IndexRule` is the
actual `TableLaws.OnStable(ExactIndex(...))` template: both indexes equal the
projection in Stable and successful Closed phases. Transient missing/stale
indexes are explicitly permitted; successful publication restores exactness.

`CheckedActions.Safe` is a weakest-precondition judgment over the REAL
`Data.operate` result. Its terminal obligation is `Model.Indexes(working)`;
there is no runtime final-state check or assumed certificate. `ClientProof`
constructs the operation/working-layout proofs and the terminal row equalities.
`safe` proves every observed execution prefix, and `execution_trace` connects
that proof to ordinary `Requirements.Certifies`, all installed laws, technical
publication checks and stable-state validity. The other user's record/index
remains unchanged. The proof is universal over every valid initial state,
context, argument and observation depth, not a single seed execution.

The example intentionally supports one Boolean availability row per user and two
fixed principals. This is the representative certified projection application;
it does not claim automatic invariant proofs for arbitrary tables or indexes.
The ordinary generic helpers remain unchanged in scope. `Completion` proves
termination even on arbitrary invalid states and arbitrarily long finite key
lists, using an actual-observation-dependent witness; it never assumes that
`EnumerateKeys` returns the valid-state singleton or uses a host quota as proof.

The audit controls in `negative_cases.py` adapt the actual operation/layout
proofs to omitted and forged maintenance. Their independent permission-only
proofs establish `permitted_all_prefixes` on ALL valid states and observation
depths. Their full certificates then fail specifically at the terminal
ExactIndex row equality in `set_alice`, rather than at an unrelated stale
permission proof. A third variant reads Bob's index as Alice; it fails at the
first `query_alice` permission obligation. The real host rejects all three and
subsequent queries verify no state changed.

Run the focused gate after a release build, under the shared lock:

```sh
flock /tmp/jaydb2-experiments-heavy.lock env TMPDIR="$PWD/build/library/tmp" \
  python3 -B applications/indexed/run_check.py
```

`check.py` only packages a local proof root for inspection. `run_check.py` runs
both official checkers on the real certificate/termination/seed and on each
maintenance negative's independent ordinary permission proof, checks intended
full-certificate failures in both modes, then runs the actual restricted host
session. All generated roots and detailed diagnostics stay in `build/library`.
The host is launched with hostile inherited `BENDRTS` flags, exercising the
accepted shared environment-policy fix on real indexed requests.

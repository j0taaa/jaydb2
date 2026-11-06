# Copyable certified application starters

Export a working application rather than writing a certificate from an empty
file. The exporter copies the existing task application's accepted programs,
proofs, administrator policy and seed. It does not edit the database, relax its
laws, add a proof axiom or replace a checker.

Run from the JayDB2 checkout after [installation](../../INSTALL.md):

```sh
python3 -B examples/starter/create.py build/my-tasks --profile crud
python3 -B examples/starter/create.py build/my-conditional-tasks --profile conditional
```

Destinations must not exist; existing files and symlinks are never overwritten.
Each directory is an editable application package. The database supplies its
reserved core modules at admission, as it does for the original application.
Your checked-out JayDB2 installation remains required.

| Profile | Example operations | Relevant proof pattern |
| --- | --- | --- |
| `crud` | `list`, `view`, `save`, `conclude`, `remove`, `cancel` | Actual operation permissions, owner-preserving full rows, all continuations and refusal rollback |
| `conditional` | `insert`, `replace_open`, `cas`, `inspect`, `pair`, `open`, `drop` | Optional ordinary query/mutation helpers, actual read permissions, conditional-write continuations and finite list composition |

Both use the existing per-person table policy. Alice and Bob are fixed demo
principals with public `alice-token` / `bob-token` credentials. They are a
starting point for learning, not production credential management.

`ClientProof.bend` is the ordinary concrete-request certificate.
`PreparedProof.bend` changes only the documented certificate wrapper to pass
quantified `ctx` and `args` into the same existing parameterized `certify` lemma.
It proves the stronger universal target required by preparation, not a weaker
application policy. Pass it as `proof` to prepare; execute the returned handle
with explicit current credentials and actual arguments. See the
[TypeScript client](../../clients/typescript/README.md).

## Validate the actual exported source

The check command runs both unmodified official checkers, including the seed's
initial validity proof, then a real native prepared session. It also alters the
actual program to read Bob's table or write an unauthorized owner/table with the
unchanged certificate. Both modes must reject these at proof obligations; the
live service must reject admission and preserve the original handle/state.
A changed terminal value may legitimately satisfy the same safety proof; these
controls specifically exercise law-breaking edits, not arbitrary textual edits.

The caller holds the usual heavy-work lock exactly once:

```sh
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock \
  python3 -B examples/starter/check.py build/my-tasks)
```

To validate fresh copies of both supplied templates:

```sh
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock \
  python3 -B examples/starter/check.py --all)
```

The commands expect a built controller and the pinned official tools. The
launcher uses the documented unlimited hard/soft stack setup. Development-only
checker timeouts are not database execution deadlines. Logs are retained in the
project's `.check/`; the `--all` runner copies them to `build/starter/crud/` and
`build/starter/conditional/` before removing its temporary exports.

Cheap packaging checks need no Bend process or compiler:

```sh
python3 -B -m unittest discover -s examples/starter -p test_starter.py -v
```

Read the [program and proof guide](../../docs/programs-and-proofs.md) for which
files to change and which obligations need to remain true. The starter's tests
exercise its supplied command vocabulary. Once you change that vocabulary,
adapt its positive and causal negative cases to your new program.

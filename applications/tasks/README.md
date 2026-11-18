# Personal tasks on JayDB2

A reference application separate from the kernel. Its program, policy, seed,
and certificate are Bend. `app.py` is only a terminal client: it keeps a real
instance of the Rust executable open and exchanges messages through pipes.

## Run

Install the tools following [INSTALL.md](../../INSTALL.md) and build the
database with `make build` at the root. Then:

```sh
python3 -B applications/tasks/app.py
```

To use another installed database checkout:

```sh
python3 -B applications/tasks/app.py --database-root /path/to/jaydb2
```

The application defaults to `alice-token`. Seed credentials are public for
demonstration: Alice and Bob start with empty tables. Example session:

```text
save t1 "Buy bread"
list
view t1
conclude t1
view t1
user bob-token
list
save t1 "Review report"
user alice-token
cancel t1 "Title to discard" true
view t1
remove t1
exit
```

`list` returns IDs; `view` returns title, ID, owner, and completion.
`save ID "title" [true|false]` creates or replaces a task. `conclude` retains
the title and marks the task complete within one transaction. `cancel`
performs a real write and refuses; the prior publication remains. `user`
changes the credential sent by the client; the database computes authenticated
identity for every call.

Alice and Bob may use the same ID `t1`: they are separate tasks. The default volatile session uses
one RAM database process. Exiting that session loses its data; the next run
reloads the seed. The explicit persistent workspace below survives exit. Each admitted call again passes official checking and compilation and
can take several seconds. Message (including code and proof), state, and
response have the configuration's three logical limits: 32768, 65536, and
32768 canonical bytes. Normal official-tool limitations still apply.

## Persistent workspace and TypeScript client

Use a new workspace once, then explicitly reopen it. The Node 24 TypeScript
application uses the optional [thin client](../../clients/typescript/README.md)
and the same unchanged `Client.bend` and `ClientProof.bend` as the Python client.
It requires no npm install or Python client process at runtime:

```sh
node applications/tasks/tasks.ts --workspace .build/tasks/personal --storage-mode create --command save t1 "Buy bread"
node applications/tasks/tasks.ts --workspace .build/tasks/personal --storage-mode open --command list
node applications/tasks/tasks.ts --workspace .build/tasks/personal --storage-mode open --command conclude t1
node applications/tasks/tasks.ts --workspace .build/tasks/personal --storage-mode open --command view t1
node applications/tasks/tasks.ts --workspace .build/tasks/personal --storage-mode open --credential bob-token --command list
```

Each command starts and closes one database process. Open loads a checkpoint
and replays subsequent WAL records. Each command authenticates and submits
its concrete certificate. The client does not retry writes.
`--command` prints one JSON response: exit 0 is success, 2 is a canonical
non-success response such as authentication/refusal, and 1 is a startup/transport
error whose write outcome may be unknown. `--help` describes the command syntax.
Put options before `--command`; shell quotes keep titles in one argument.

For longer interactive sessions, the Python client can open exactly that same
workspace, reducing repeated process startup:

```sh
python3 -B applications/tasks/app.py --workspace .build/tasks/personal --storage-mode open
```

It also accepts `--command`, `--credential`, and `--threads` with the same meaning.
Without workspace options it retains its existing disposable RAM behavior.
`--demo` always uses a disposable volatile instance. Both clients default to one
native worker for these small commands.

Workspace layout is `app/` (frozen example modules) and `db/` (owned by JayDB).
Create requires a new workspace. Open uses the exact database executable and
durable environment without a seed. A failed create may leave a partial
workspace. One process owns the database directory at a time. Exit the
interactive client before opening it from another command.

Alice and Bob use public demonstration credentials. The example
`migrations/` adds an optional integer priority through the host's checked
[administrator migration socket](../../tools/service/SIMPLE_SERVICE.md#checked-migrations).

## Application laws

- Each user accesses only the table named after their authenticated identity,
  including reads followed by refusal.
- Every task row has `owner` equal to that table's owner, who must exist
  in the user registry.
- The program neither modifies the registry nor grants access to other tables.
  A write supplies the complete row with its authenticated owner.
- The schema requires `id`, `title`, `completed`, and `owner` with their
  declared types.

These are application policies, not new kernel policies. To keep the example
small, configuration declares Alice and Bob's tables. An administrator can
change configuration/seed and supply the corresponding proofs. Ownership also
holds in working states before publication; `Policy.Rule` makes this choice
explicit.

## Writing and modifying proofs

| File | Responsibility |
| --- | --- |
| `Client.bend` | Pure program and application commands. Data arrives only through database operations. |
| `ClientProof.bend` | Each command's permission and bindings to actual `Bindings.certificate` and `Bindings.terminates` targets. |
| `Policy.bend` | Identity and owner laws independent of client commands. |
| `Ownership.bend` | Proof that authorized operations preserve owners and the authenticated registry. Uses actual `Data.operate`. |
| `Proofs.bend` | Composition of permissions across all prefixes, finalization with the actual resulting-state invariant, and termination. |
| `Configuration.bend` / `Seed.bend` | Schema, configuration, and a separate initial-validity proof. |

A new command's specific work belongs in `command_safe`: supply the operation
permission and continuation proof. `Proofs.safe` connects this to all actual
observations; each program need not repeat prefix induction. `Proofs.finalize`
uses the invariant of the state actually obtained, without requiring every
imaginary state to be valid.

Pure functions format responses as `Data.Value`. Terminal handlers only wrap
these values in `Finish`. This reduces proof cases without hiding accesses.
For example, `conclude` uses the same composition for a read followed by a write.

A parameterized lemma (`certify`) constructs the certificate before it is
applied to the actual context and arguments. This avoids repeatedly evaluating
concrete reification inside the proof; it changes neither the target nor
BendTT fuel. Depth `3` in `Safe` is a mathematical witness for this program
(at most two operations and a terminal action), not a database execution limit.

The client packages modules in a temporary directory. It reuses existing
`proof/Orders.bend` and `proof/Foundations.bend`, adjusting their relative
imports for the package. Their bodies are not duplicated in this folder. The
server freezes and checks this set with official Bend/Safe/BendTT. Database
state is not placed in files used to verify the client.

## Local check

```sh
python3 -B applications/tasks/check.py
```

This uses the actual client and database. It checks CRUD, completion,
Alice/Bob isolation, authentication, refusal, and rollback. Then it sends two
mutated sources with the original proof: a read of Bob followed by refusal,
and a write with an invented owner. Both must be rejected by `PRIMARY_CHECK`
without changing state. A third negative attempts initialization with Alice's
task but no registered Alice: state is structurally valid, but its ownership
proof must be rejected.

`--database-root` also works here. No GitHub Actions workflow is attached. This
is a local test and not part of server execution.

The scope of the eight laws and integration assumptions remain those in
[proof guide](../../proof/README.md). This application adds no
compiler, verifier, runtime, physical quota, or database parser.

## Accessory acceptance and regular use

The reusable native workflow is:

```sh
flock /tmp/jaydb2-experiments-heavy.lock python3 -B -m unittest tests.accessories.test_tasks_native -v
```

It starts in TypeScript, saves a task, removes the seed, reopens from Python,
concludes the task, verifies refused writes roll back, verifies Bob's isolation,
and reopens again through TypeScript to check both owners' tasks. Invalid
credentials, canonical non-success CLI exits and a second `create` are also
checked. The lightweight `tests.accessories.test_tasks` tests need no Bend tools. After
`npm ci --prefix clients/typescript`, typecheck the actual TS consumer with
`clients/typescript/node_modules/.bin/tsc -p applications/tasks/tsconfig.json`.
These accessories do not change the application's Bend sources or its laws.

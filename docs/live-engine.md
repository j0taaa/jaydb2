# Live engine (experimental branch `experimental/live-engine`)

This branch changes how the host runs certified programs. The contract, the
laws, the certificates and admission are unchanged. What changes is where the
state lives and how long workers live.

| Today (`main`) | Live engine |
| - | - |
| Every call ships the whole canonical state to a fresh process and receives a whole new state back | The host keeps the state in an indexed, versioned store; the worker asks for one data operation at a time |
| One fresh process per call | Prepared programs run in long-lived worker processes that serve many requests |
| Strictly serial | Many connections run transactions concurrently; commits are serializable |
| Schema and laws frozen for the instance | An administrator can migrate to a new configuration with a checked migration |
| Complete-image file rewritten per commit | Write-ahead log of write sets + background checkpoints |

## Why this is possible without changing the contract

A program never touches the state. `S.Program` builds an `S.Action` tree whose
only contact with data is `Access{operation, resume}` with one of seven
`D.Operation`s (read cell, existence, count, keys, define row, define column,
remove row). `S.step` answers each operation with `D.operate` on the working
state. If the host answers every operation exactly as `D.operate` would on the
transaction's working state, the trace `τ` the worker produces is the same trace
the existing theorems talk about. The certificate quantifies over *every* valid
initial state, so it still applies.

## Components

### 1. Store (`server/store/`)

* Logical state = one ordered map per collection (each application table and
  the user registry), key → row. Maps are persistent (`imbl::OrdMap`), so a
  snapshot is an O(1) clone and readers never block writers.
* Each committed version has a sequence number (LSN). A transaction reads from
  the snapshot it started at, plus its own overlay of writes.
* The seven operations reproduce `D.operate` exactly, including its
  validation and error cases (`contract/Data.bend`). Differential tests compare
  them with the Bend reference.
* A credential index (credential → user id) serves authentication.
* Final technical conditions are maintained incrementally: per-row structure is
  checked on every write (as `D.operate` already does), credential
  nonempty/unique via the index, and the canonical state size as
  `base + Σ row contribution` (the canonical encoding is additive: tag + u64
  count + elements).

### 2. Remote worker ABI (`src/Remote.bend`, `native/effects.*`)

The worker no longer receives or returns state. All frames on the worker's
stdin/stdout are `u64 big-endian length || payload`.

* host → worker, request: for a prepared program,
  `u64 len(registry) || registry bytes || original request body`; for a direct
  program, the original request body.
* worker → host, data operation: `0x02 || canonical value of the operation`.
  The host replies with one frame holding the canonical value of the answer.
* worker → host, end of request: `0x01 || response bytes` (Commit) or
  `0x00 || response bytes` (Keep).

Operations and answers are records (fields in exactly this order); the
collection is `absent` for the user registry and the table name otherwise:

| Operation | Value |
| - | - |
| authenticate | `{op: "authenticate", credential}` |
| read cell | `{op: "read_cell", collection, key, column}` |
| existence | `{op: "existence", collection, key}` |
| count | `{op: "count", collection}` |
| keys | `{op: "keys", collection}` |
| define row | `{op: "define_row", collection, key, fields: {..row record..}}` |
| define column | `{op: "define_column", collection, key, column, value}` |
| remove row | `{op: "remove_row", collection, key}` |

| Answer | Value |
| - | - |
| `RowAbsent` | `{result: "row_absent"}` |
| `Cell` | `{result: "cell", value}` |
| `Existence` | `{result: "existence", exists}` |
| `Count` | `{result: "count", count}` (integer) |
| `Keys` | `{result: "keys", keys: [text...]}` |
| `Changed` | `{result: "changed"}` |
| `FailureData` | `{result: "data_error"}` |
| user found | `{result: "user", id, kind, credential}` |
| no user | `{result: "no_user"}` |

Authentication asks the host for the user row holding the credential and then
runs the unchanged `D.authenticate` over a one-row registry, so a wrong row from
the host cannot produce a context for a different credential.

The worker checks the response limit and response validity in Bend, as
`R.finalize` does. The state-side checks of `R.finalize` (structure, state
limit) run in the host at commit, *before* the response checks, preserving
`R.finalize`'s order: a structural failure gives `data`, an oversized state
gives `limit`.

A persistent worker loops: read request → run → answer operations → write the
final frame → read the next request; EOF ends the process. Direct (ordinary)
programs bake the request's context and arguments into their Book, so they use
the same ABI but serve one request and exit.

### 3. Transactions and concurrency

* Each connection is a FIFO session. A session writes the response before
  starting its next request. Stdin/stdout remains one session. `--listen SOCKET`
  serves the same frames over a Unix socket, with one thread per connection.
* `--concurrency N` bounds simultaneous socket transactions, including direct
  compilation. The default is available CPU parallelism, capped at 128. Prepared
  handles start workers on demand and reuse idle workers. A handle can grow up
  to the execution bound. With concurrent execution each native process defaults
  to one Bend runtime thread unless `--threads` is set. CUDA uses one execution
  slot per instance.
* Optimistic concurrency control. A transaction records the rows, collection
  membership and credentials it observes. At commit its observations and written
  rows are checked against writes since its snapshot. Conflicts rerun the whole
  request on a fresh snapshot. After three conflicts a request queues for
  exclusive execution, as do prepares and invalidations. Once queued,
  exclusive work runs in FIFO order ahead of new shared attempts.
* A single committer validates pending writes against the successive snapshots
  in commit order. It appends the accepted write sets in one WAL batch and
  publishes the final snapshot after the batch is durable. Responses are ready
  only after that publication. Read-only successes answer from their already
  durable snapshot, consuming no LSN or WAL record.
* Every attempt reads a consistent snapshot of a valid published state, so
  each prefix is a trace covered by the certificate. A validated write observes
  what it would observe at its commit point. A read-only call takes effect at its
  snapshot acquisition. This makes the execution strictly serializable.
* The host pins snapshot LSNs through execution and commit. Every 256 write
  commits, it prunes row and credential versions at or before the oldest pinned
  LSN. No active transaction needs those versions for validation.

### 4. Durability and failures (`server/wal.rs`)

* Storage directory: `checkpoint-<lsn>` (canonical state bytes, LSN,
  configuration descriptor, checksum) and a write-ahead log of records
  `length || crc32c || lsn || kind || payload`. A commit record holds the write
  set: `(collection, key, row canonical bytes | removed)`.
* Recovery loads the newest valid checkpoint and replays later records in LSN
  order. A torn or corrupt record at the tail is discarded (it was never
  acknowledged); corruption followed by valid records refuses to open.
* Checkpoints are scheduled from the final snapshot of a batch when it crosses
  a 256-commit boundary and the checkpoint queue has room. The background
  writer saves a temp file, syncs it, renames it and syncs the directory before
  reclaiming older log segments.

Guarantees:

1. An acknowledged success survives process crash and power loss (given an
   honest `fdatasync`).
2. Atomicity: after recovery a transaction's writes are all present or all
   absent.
3. Recovery yields a prefix of the commit order that contains every
   acknowledged transaction.
4. A worker crash or protocol violation discards that transaction, replaces the
   worker and answers `failure`; published state is unchanged.
5. If the log cannot be written or synced the service stops (fail-stop) instead
   of guessing.

### 5. Schema changes

An administrator submits, over `--admin-socket`, a new configuration file, a
Bend migration `migrate(s: D.State) -> D.State` and a proof that for every `s`
valid under the old configuration, the stable laws of the new configuration
hold for `migrate(s)`. Structure and state limit of the result are checked at
runtime (as `R.Valid` splits them today). Both official checkers must accept the
migration Book. The host then quiesces new transactions, runs the migration on
the whole state (the one place where whole-state processing is acceptable),
writes the new state and configuration as one durable epoch record/checkpoint,
switches configuration, retires all workers and prepared registrations, and
resumes.

## Trust changes (honest list)

New trusted host code, supported by tests rather than proofs:

* the store's implementation of `D.operate` and of the incremental structure
  and size checks (differential tests against the Bend reference);
* OCC validation and the committer;
* the log, checkpoint and recovery;
* the `serve` loop effect in C.

The contract theorems are untouched and still verified. The old whole-state
worker modules stay in the tree because the contract proofs refer to them.

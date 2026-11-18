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
* worker → host, end of request: `0x01 || response bytes` (Commit),
  `0x03 || response bytes` (the program proposed success but the response
  checks failed: the host still runs the state checks first, never commits) or
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
the same ABI but serve one request and exit. An operation payload is limited
to 1 GiB, a physical host bound: a program may write a value larger than the
state limit and remove it before finishing, so the state limit itself is only
checked at commit. A larger operation frame is a protocol violation and the
host kills the worker.

Execution has no time budget. A stalled worker blocks its session and any
queued exclusive work, including prepare installation and migration, until it
ends.

### 3. Transactions and concurrency

* Each connection is a FIFO session. A session writes the response before
  starting its next request. Stdin/stdout remains one session. `--listen SOCKET`
  serves the same frames over a Unix socket, with one thread per connection
  and up to 128 live client sessions. Extra connections are closed. Transient
  accept failures are logged and retried.
* `--concurrency N` bounds simultaneous socket transactions, including direct
  compilation. The default is available CPU parallelism, capped at 128. Prepared
  handles start workers on demand and reuse idle workers. The instance keeps
  at most one idle worker per execution slot and evicts the least recently used
  idle worker whenever the pool exceeds that budget. With concurrent execution,
  each native process defaults to one Bend runtime thread unless `--threads`
  is set. CUDA uses one execution slot per instance.
* Optimistic concurrency control. A transaction records the rows, collection
  membership and credentials it observes. At commit its observations and written
  rows are checked against writes since its snapshot. Conflicts rerun the whole
  request on a fresh snapshot. After three conflicts a request queues for
  exclusive execution. Invalidations and prepare installation also queue for
  exclusive execution, which runs in FIFO order ahead of new shared attempts.
  Prepare stages, checks and compiles against a pinned environment in a separate
  pool sized to the execution bound. Installation checks that the epoch, registry
  and authentication view still match the controller's inputs. If any changed,
  the prepare returns `failure` and the registration is discarded.
* The dispatcher applies the active epoch's message limit to each selected
  declaration in FIFO order. An oversized declaration receives the canonical
  `limit` response and ends the session. Stdin can read ahead up to eight items
  and 1 MiB of bodies. Larger bodies wait for dispatch before being read.
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

* Storage contains `checkpoint-<lsn>` (canonical state bytes, LSN,
  configuration descriptor, checksum) and a write-ahead log with one frame per
  append batch. The frame starts with a length and CRC-32, followed by the
  records. The first record repeats the batch length after its LSN and kind.
  The checksum covers the entire frame body. A commit record holds the write
  set `(collection, key, row canonical bytes | removed)`.
* Recovery loads the newest valid checkpoint and replays later records in LSN
  order. Recovery discards a torn or corrupt tail batch in full and refuses
  to open if a valid batch follows the corruption.
* Checkpoints are scheduled from the final snapshot of a batch when it crosses
  a 256-LSN boundary and the checkpoint queue has room. The background
  writer saves a temp file, syncs it, renames it and syncs the directory.
  It keeps the two most recent checkpoints and reclaims only segments fully
  covered by the older one.

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

Start the host with `--admin-socket PATH` to accept migrations on a Unix
socket with mode `0600`. It is separate from client sessions and from
`--inspect-socket`. Each connection takes one UTF-8 JSON line (including the
newline, at most 65,536 bytes) and returns one JSON line before closing.
Paths are resolved by the host from its working directory.

```json
{"command":"migrate","configuration":"/path/new/Configuration.bend","migration":"/path/Migration.bend"}
```

A successful response is `{"status":"success","lsn":42}`, where `lsn` is the
published epoch's sequence number. A rejected request returns
`{"status":"error","code":"data","message":"migration returned data"}`, with
a code and diagnostic for the actual error.

The migration module defines `migrate(s: D.State) -> D.State` and proves that
it preserves the new configuration's stable laws for every state valid under
the active configuration. The host stages and compiles the migration and new
configuration with both official checkers while clients continue running.
Then it queues for the existing exclusive execution permit, which blocks new
shared attempts. In-flight attempts release their permits after execution and
any committer reply. Exclusive work runs in queue order. The migration reads the entire canonical
state, checks the result's structure and state limit, and loads it with the
new schema from the conventional startup exporter.

In durable mode the committer appends and syncs one WAL epoch record with the
new descriptor and state before publishing the snapshot. Checkpoints each
carry the descriptor of their own snapshot. Before admitting more work, the
host installs the new authentication and control programs, frozen compilation
environment, and logical limits. It clears the prepared registry and reaps
all its workers. Old handles receive the usual unknown-handle response
(`failure` for an authenticated execution request). Clients can reuse their
connections and prepare again under the new configuration.

Rejections before writing the epoch leave the database and registrations
intact. WAL write or sync failures stop the process. Open a migrated database
with `--storage-mode open` and the new configuration using the same frozen
host/tooling identity. Recovery loads the latest epoch and replays its later
commits. The previous configuration fails with the existing descriptor
mismatch when its descriptor differs. Administrators can migrate in volatile
mode too, with the same cutover semantics in memory.

## Trust changes (honest list)

The checked remote refinement proof connects the worker's reply decoder to
`S.step` when the host applies `D.operate` to the transaction's current working
state and sends the ABI-ordered answer within the worker's wire and count
bounds. For finite prefixes with representable exchanges, the proof transfers
certificate coverage and preserves the working state, operation events and
terminal response proposal. The Rust operation-frame decoder and answer encoder
remain part of the trusted host bridge.

New trusted host code, supported by tests rather than proofs:

* the store's implementation of `D.operate` and of the incremental structure
  and size checks (differential tests against the Bend reference);
* OCC validation and the committer;
* the log, checkpoint and recovery;
* the `serve` loop effect in C.

As on `main`, the native worker compiled from the admitted Book is trusted
(T2): the host checks frame shape, authentication order and the final checks,
but cannot tell whether a faulty worker's operations are the admitted program's.
The refinement proof covers the checked Bend side of that worker.

For prepared execution, T3 requires the host to forward only the controller-issued
entry for the requested handle, or an empty registry when no live entry exists.

The contract theorems are untouched and still verified. The old whole-state
worker modules stay in the tree because the contract proofs refer to them.

# Optional administrator request timing

```
mkdir -p build
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 2 \
  --timing-log build/service.ndjson
```

`--timing-log FILE` appends administrator NDJSON; `-` writes to stderr with
ordinary diagnostics. A new file has mode 0600; existing file permissions are
unchanged. The parent directory must exist. Startup fails if the file cannot
be opened. A write failure prints `TIMING_LOG` and disables that sink without
changing request execution, publication or client responses. Logs have no
flush or durability promise. Treat them as administrator data: they contain
exact authenticated principal IDs. Workers do not inherit the log descriptor.
No logging is enabled by default. Quota enforcement is excluded from integration.

A completed request produces a record such as:

```json
{"format":"jaydb-service-timing-v1","sequence":2,"principal":"alice","elapsed_ns":"42000000","retries":0,"wal_batch":1}
```

- `sequence` counts timing starts from one per process. Concurrent requests
  can finish and log out of sequence.
- `principal` is the identity authenticated on the final attempt, or null
  when authentication did not succeed. An authenticated empty ID is an
  empty string.
- `elapsed_ns` is monotonic wall time in nanoseconds, encoded as a decimal
  string.
- `retries` counts optimistic concurrency conflicts that reran the request.
- `wal_batch` is the number of write records in the durable batch that
  published this request's write. It is zero for other outcomes.

The counter resets on restart. Existing logs are appended to, so records from
separate instances can have the same sequence number.

## Measurement boundary

Timing starts after the complete frame obtains its initial execution permit
and before authentication. Preparation starts timing after taking its initial
snapshot and environment. Reception, initial queue waits, startup and terminal
framing events are outside the interval.

Timing includes authentication, applicable artifact checks, admission and
compilation, worker exchanges, direct-worker cleanup and result readiness.
It includes OCC retries and their later permit waits. For writes it includes
committer waiting and durable publication. Prepare includes waiting for
exclusive installation. The host stamps completion before serializing or writing the record, final
inspection and client delivery. A kill, panic, fail-stop or stalled worker can leave no completion record.

## Authentication and proof scope

The ordinary preprocessing helper supplies the principal from the same checked
context that produces the generated instance. The normal prepared execution
path records the principal from the snapshot's credential index. The worker
authenticates the user again through the private operation protocol.

The two `Messages` principal laws prove the preprocessing helper's
source-level identity binding. The host credential lookup, Rust and native
byte exchange, clock, timing hooks and log writes remain trusted.

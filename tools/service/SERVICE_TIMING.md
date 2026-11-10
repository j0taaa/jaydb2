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

A completed selected request produces a record such as:

```json
{"format":"jaydb-service-timing-v1","sequence":2,"principal":"alice","elapsed_ns":"42000000"}
```

`sequence` is dispatch order, starting at one per service instance. `principal`
is null if authentication did not succeed; an authenticated empty ID is the empty string. Nanoseconds are exact
decimal strings. The log is an observation, not an acknowledgment, result cache,
rollback assertion, or new protocol response.

## Measurement boundary

The metric is monotonic wall service time, not CPU usage. It starts when a
complete frame is selected for service, before decoding and authentication.
Reception, prior queue waits, startup and terminal framing events are excluded.

The interval includes snapshot packet copying, authentication, artifact checks,
proof admission/compilation where applicable, native execution, child and pipe
cleanup, proposal validation and publication. Completion is stamped
at `publish_with_ready`: after any durable snapshot commit and RAM publication,
before final inspection and client delivery. A fatal commit uncertainty before
that hook is measured once at the fatal return; service still stops with no
response or later dispatch. A log cannot determine whether an uncertain commit
reached storage.

Intermediate inspection during execution remains part of service time; final
inspection, log serialization/write/lock waiting, and client write/flush are
excluded. A process kill, panic or request that never finishes can leave no
completion record. No cancellation or deadline is added. The sequence counter
resets on restart, including durable reopen. An existing log file is appended to, so separate instances can produce
the same sequence numbers. The counter is process-local and not persistent.

## Authentication transport and proof scope

The private native authenticator success format is:

```
1 || u64be(id_utf8_length) || exact_context_id_utf8
  || u64be(code_length) || code || u64be(proof_length) || proof
  || u64be(instance_length) || instance || links_remainder
```

Rejection remains `0 || ordinary_response_frame`; invalid internal transport
remains `2`. `Messages.authentication` obtains principal and generated instance
from the same freshly authenticated `Input.Analysis.Received` context. All
ordinary and prepared consumers parse that exact format. Current
credentials and administrator laws still apply; no client identity assertion,
authority, cached authentication or admission bypass is introduced.

The two Messages principal laws prove this source-level identity binding.
The Rust/Node/native byte bridge, monotonic clock, completion hooks and OS log
writes remain trusted host behavior covered by controlled-clock and actual
worker tests. Existing serial theorems are not silently extended to
prove those effects. All three canonical byte limits and ordinary response
bytes remain unchanged.

# Opt-in service timing and soft quotas

Ordinary operation has no timing observer or quota. All three canonical byte
limits, administrator laws, exact proof/source/argument binding, error precedence,
and fresh worker isolation remain in place.

```
mkdir -p build
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1 --timing-log build/service.ndjson

./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --timing-log - \
  --quota-period-ms 60000 --quota-budget-ms 10000
```

`--timing-log FILE` appends administrator NDJSON. A new file is created with
mode 0600; an existing file retains its permissions. `-` writes NDJSON to stderr,
interspersed with ordinary diagnostics. The parent directory must exist.
Failure to open the requested log aborts startup. A later write failure emits
`TIMING_LOG` to stderr and disables logging without changing any
publication, response, or quota charge. Logging has no flush/durability promise.
Client stdout contains only existing framed responses and opt-in control receipts.
Treat the file as administrator data: it includes authenticated principal IDs.

Each completed selected request produces one record, for example:

```json
{"format":"jaydb-service-timing-v1","sequence":1,"principal":"alice","elapsed_ns":"42000000","outcome":"ordinary","quota":null}
```

Nanoseconds and quota numbers are decimal strings (not lossy JSON numbers).
Sequence starts at 1 for each instance. Null principal means authentication did
not succeed. Quotas add `period`, `period_ns`, `budget_ns`, `used_ns` in `quota`.
`outcome` is `ordinary` for any ordinary/prepared response including failures,
or `quota` for a host policy denial. This log never replaces a response.

## Metric and lifecycle

One metric is monotonic elapsed service time, not CPU time. Selection starts
only after a complete bounded request frame is dispatched. The interval includes
extension parsing, state packet copying, authentication (and current preprocessing),
admission/checking, compilation, execution, artifact validation, process/pipe
cleanup, proposal checking, and publication. Any durable commit must finish
before completion. Completion takes one clock sample after all service work,
before completed inspection/log output, any wait for ordered delivery, or client
response writes/flushes. Intermediate diagnostic inspection during service is
included. Queue waits, frame reception, response delivery, startup and shutdown
are excluded. Terminal framing errors never become selected service attempts;
they produce their existing response with no timing record.

`ServicePolicy::selected`, `authenticated`, `completed` are separate host hooks.
The coordinator owns the clock, counters, and non-cloneable `Attempt` tokens.
`Database::execute` is called only for a selected Request and carries its token
in `ServiceCompletion`; `publish_completed` consumes it after publication.
EOF and terminal framing events never call `execute`. The accepted serial
scheduler flushes each response before selecting the next request.
For later concurrency it may retain tokens for active requests; it must complete
each token after cleanup/durability/publication and before delivery/order waits.
An uncertain commit stops dispatch; it is never converted into a quota denial
or a claim of rollback. The accepted scheduling and persistence prerequisites
are integrated. Optional
`--storage DIR --storage-mode create|open` performs the durable commit inside
this same interval. At the actual `publish_with_ready` callback, the owned
policy consumes the token immediately after durable and RAM publication.
If an uncertain commit returns fatally before readiness, the remaining token
is charged once at that fatal return; if the callback already ran it is never
charged twice. Fatal attempts emit no response and dispatch stops. Logs may be
written on this fatal return and carry no acknowledgment/rollback promise.

## Accounting and protocol extension

Both quota options must be positive uint64 milliseconds and supplied together.
Quota measurement works with or without a log. A process-local monotonic origin
is established after database initialization. Period `floor(elapsed / period)`
is shared by users, with half-open intervals `[kP,(k+1)P)`. Every principal starts
with zero charged time. Authentication uses the current selected snapshot.
After successful authentication, before admission, prepared registry operations,
or program start, the request proceeds exactly when that principal's completed
charges in the current period are strictly less than its budget.

Exhaustion returns the canonical *encoding* of this host control receipt:

```json
{"status":"quota","value":null}
```

Like `prepared`/`invalidated`, this is explicitly outside `S.Status` and
`S.Response`. It is enabled only by administrator quota policy, not a client
credential/flag. It is never a canonical `limit`, `failure` or `certificate`
response. Like prepared receipts, it goes through bounded control response
preparation and obeys the canonical response-size ceiling. Its fixed 53-byte
body is shorter than certificate/null (59 bytes), which a valid configuration
must already accommodate. The ordinary state/message/response ceilings are
unchanged.
No program runs, handle changes, or state publication occurs on quota denial.
Canonical decoding errors, invalid extension opcodes and authentication
errors retain precedence. After fresh authentication, quota denial takes
precedence over admission, handle errors and prepared-control field validation
(including a nonempty proof on execute/invalidate). Those later field errors
return `input` when policy permits the attempt; they still have an authenticated
principal.

At completion, charge the *entire* measured interval once to the initially
authenticated principal in the completion period. Include certificate/handle
rejections, ordinary refusals, data/limit/runtime failures and quota denial
itself, including authenticated prepared-control `input` errors. Failed
authentication, canonical decoding/opcode errors and pre-authentication host
failures have no principal and are not charged. A credential exchange charges
its initial actor; the next selection authenticates again, so a reused
credential can identify another user. IDs are exact strings, without case folding
or delimiter keys. Deleting/recreating the same ID shares that period's bucket.
Counters clear on period rollover and process restart, including durable
reopening; these quotas have no restart-survival or anti-restart guarantee.
A request crossing a boundary charges its full duration to its completion period,
even if denied against an earlier period. Earlier periods are not retained.

There are no reservations, CPU metering, per-program instrumentation, worker
changes, deadlines or cancellation. A request admitted below budget may run
arbitrarily long. Already-running requests finish, even after another completion
exhausts the bucket; time overshoot is unbounded, in serial or concurrent service.
A request that never completes is never charged. Duration addition saturates at
Rust's representable maximum (which is above every configurable budget), so it
cannot wrap into credit. Per-period memory is one entry per distinct completed
authenticated ID; there is no additional logical resource limit or eviction.

## Contract/proof boundary

The original serial eight-law theorem describes ordinary processing without
quota policy. It does not establish that every otherwise-processable request
will run in the quota extension. The extended host selects either (a) the
unchanged ordinary/prepared path after a policy pass, or (b) a policy receipt
with no admission/start/publication. Progress for (b) means completing/delivering
a policy decision, not completing the requested program. Logging is an external
observation, not a new operation or application-state field.

Private authentication success is now exactly:

```
1 || u64be(id_utf8_length) || exact_context_id_utf8
  || u64be(code_length) || code || u64be(proof_length) || proof
  || u64be(instance_length) || instance || links_remainder
```

Rejection remains `0 || ordinary_response_frame`, invalid internal transport
remains `2`. `Messages.authentication` obtains both principal bytes and generated
instance from the same `Input.Analysis.Received` context. It never parses identity
from generated source. `Messages.principal_is_authenticated_id` and
`Messages.authentication_binds_principal_and_instance` check that binding in both
official verifiers. This strengthens the private transport; no client identity
assertion, certificate bypass, or source/proof substitution is added.

Rust hook order, the monotonic OS clock, fresh snapshot/worker byte correspondence,
fixed-period arithmetic and log delivery remain trusted host refinement contracts,
supported by injected-clock unit tests and real official-worker integration tests.
There is no mechanized proof of Rust quota accounting or the scheduling/persistence
composition. The old theorem is not silently claimed for this new protocol.

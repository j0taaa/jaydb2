# Timing and quota experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6` (common anchor).
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Accepted prerequisites incorporated on this branch:

- Preprocessing `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`, merged as
  `0596bdc` after standalone feature checkpoint `bf32900`.
- Scheduling `23f7bcb7e8b718288a7cad869215b8acee91b005`, merged as
  `9675a22`; accepted real-CLI milestone
  `0aeaa4569dcf164844e72fc368f07eae9f022446`, merged as `93126e8`.
- Persistence ready boundary `83a9f3703345c234fe3b14363e6e14e15cb88b80`,
  merged as `5bb4f20`.

No unaccepted sibling changes were incorporated. The pinned official tools are
an immutable `.tools` symlink to `/home/jota/projects/jaydb2/.tools`. Build,
output, fault-binary, temporary and state paths are worktree-local for final
validation. No push, PR, deployment or main merge was performed.

## Supported behavior

Actual implementation and complete CLI/accounting/contract examples are in
[`SERVICE_TIMING.md`](../../tools/service/SERVICE_TIMING.md).

```
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1 --timing-log build/service.ndjson

./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --storage build/timed-db --storage-mode create \
  --timing-log - --quota-period-ms 60000 --quota-budget-ms 10000
```

The optional NDJSON observer records one monotonic elapsed interval per selected
complete request. It includes authentication, admission/checking, compilation,
execution, cleanup and durable/RAM publication. It excludes ingress/queue waits,
final inspection/log output, response ordering waits and client delivery.
Neither the log nor quota counters change program inputs, observations or state.

The paired positive-millisecond quota flags enable a soft per-authenticated-ID
fixed-period gate before admission, handle changes or program start. A completed
authenticated attempt charges its full service interval once to its initial actor
in its completion period, including failures, refusals and quota denials.
Unauthenticated/input errors have no charged actor. Periods are half-open,
process-local, aligned to service startup; counters reset at restart (including
durable reopen). Running requests finish without reservations or cancellation;
wall-time overshoot is unbounded. Same-ID recreation shares the period's bucket.

Exhaustion is an explicit `{status:"quota",value:null}` host control receipt,
outside `S.Status`; it is never a technical failure. It obeys the canonical
response-size ceiling via existing bounded control preparation: quota/null is
53 bytes, shorter than the 59-byte certificate/null error required by a valid
configuration. All three canonical ceilings remain in force. Defaults preserve
ordinary response bytes and operation semantics without observer/quota gating.

`ServicePolicy::{selected,authenticated,completed}` and injected `Clock` keep
accounting modular. `SerialService::execute` starts only at Request dispatch and
owns the token with its proposal in `ServiceCompletion`. `publish_completed`
uses the accepted `publish_with_ready` callback to consume it immediately after
durable + RAM publication, before final inspection. A fatal uncertain commit
before readiness consumes the remaining token once, logs the attempt, propagates
the fatal error and emits no response or later dispatch. An already-consumed
token is never charged again if a post-publication fault stops the host. Ordinary
operation with no timing/quota takes the accepted noop-ready publication path.
Prepared handles remain ephemeral; exact-environment durable reopening retains
the accepted persistence constraints and storage/recovery assumptions.

## Contract and proofs

Private authentication success prepends length + exact Context.id UTF-8 bytes to
the prior source/proof/instance/links metadata. Source and principal come from the
same fresh `Input.Analysis.Received` context; no generated-source identity parsing
or credential/identity caching occurs. The stage format contract and Rust parser
were committed with the native emitter in `bf32900`.

Actual new proof targets in `src/Messages.bend` are
`principal_is_authenticated_id` and
`authentication_binds_principal_and_instance`. They concern the actual native
metadata emitter. The accepted `Preprocessing.gate_preserves_exact_output` and
`single_pass_preserves_exact_output` still compare exact output through this
emitter, including the new principal prefix. `Persistence.recovered_certified_publication_is_valid`
provides the accepted recovery-preservation theorem under its storage/environment
bridge assumptions; see the persistence report for its complete premises.

The original ordinary eight-law theorem is not claimed to prove this opt-in
policy protocol or Rust accounting. Policy denial has its own host
progress/receipt contract: it completes a policy decision without admitting or
starting the program. No final validity, certificate bypass or new permission to
publish was assumed. The Rust/Node/native byte bridge, monotonic OS clock, quota
arithmetic, once-only host hook order, filesystem flush behavior and exact
serialization/environment correspondence remain explicit trusted integration
contracts, supported by the checks below. No mechanized proof of their full
composition or power-loss behavior is claimed.

## Validation

Completed before the consolidated final run:

- `cargo test --locked`: 30 combined host/clock/scheduling/storage/model tests
  passed, including controlled-clock use of the actual durable-ready callback.
- `cargo clippy --locked --all-targets -- -D warnings`: passed. Two timing
  nested-if findings were corrected before this pass.
- `make build`: passed under the shared lock on the initial feature revision.
- `python3 -B tools/check.py src/Messages.bend`: both official checkers passed
  both new identity/instance binding laws.
- `python3 -B -m unittest tests.service.test_timing -v`: all four initial
  real-worker tests passed in 55.776s before response-bound/queue/storage
  integration. Final coverage below supersedes that initial binary.

The final consolidated run is queued under
`flock /tmp/jaydb2-experiments-heavy.lock`, with
`TMPDIR="$PWD/.build/timing/tmp"`. Obsolete queued runs were canceled before
acquiring the lock; they ran no checks. Final results will replace this paragraph.
The consolidated commands are build; host tests; strict clippy; formatting;
`make verify-contract`; both-checker checks of `VERIFY.bend`,
`proof/Preprocessing.bend`, `proof/Persistence.bend`; actual default, prepared,
preprocessing differential, scheduling and timing service suites; then a separate
local `storage-fault-injection` binary with timing/persistence fault tests.

Meaningful coverage includes exact/Unicode/empty authenticated IDs; exact source,
proof, argument and current-context binding; malformed-input/auth precedence;
credential exchange on queued requests; completion-period boundary crossing;
exact exhaustion and rejection charges; restart reset with actual durable state;
certificate and native runtime failure; denied invalidation; default framing,
publication, cleanup and delivery failure; closed-output dispatch stop; absence
of client timing metadata; and actual durable precommit/uncertain/post-publication
fault behavior with one charge and no later dispatch on fatal error.

## Costs and limitations

No CPU/performance benchmark was run. Timing-only service adds two monotonic
clock samples; quota adds one authentication sample plus per-period map lookups.
NDJSON serialization/output is outside the measured interval and can delay later
selection. Intermediate inspector output during service is included. Map memory
is per distinct completed authenticated ID in the current period; rollover clears
it. There is no extra logical resource ceiling or eviction policy.

Logging is optional administrator output, with administrator-managed file growth;
write errors disable logging without undoing publication or quota accounting.
No log fsync is promised. A fatal process kill can lose logs and ephemeral quota
counters, even when state is durable. A request that never completes is never
charged. No quota persistence, CPU metering, reservations, hard deadlines,
cancellation, per-user scheduling fairness or concurrent host execution is added.
The hooks permit future certified read batches, but that composition is not
implemented/proved on this branch. Durability inherits the accepted protected
storage, flush, single-owner and frozen-environment assumptions.

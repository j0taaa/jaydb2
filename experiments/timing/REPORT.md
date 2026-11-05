# Timing and quota experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6` (common anchor).
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Accepted preprocessing prerequisite `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`
was merged as `0596bdc` after standalone feature checkpoint `bf32900`.
No sibling in-progress changes have been incorporated. Official pinned tools
are the immutable `.tools` symlink to `/home/jota/projects/jaydb2/.tools`.

Implemented behavior and CLI examples are in
[`SERVICE_TIMING.md`](../../tools/service/SERVICE_TIMING.md). This is actual
Rust service functionality with native Bend authentication metadata, not a stub.

- Optional `--timing-log FILE|-`: one monotonic elapsed service interval for
  each selected complete request, recorded as administrator NDJSON. No client
  response changes, application fields, per-program effects or worker changes.
- Optional paired `--quota-period-ms N --quota-budget-ms N`: fresh snapshot
  authentication, strict below-budget check before admission/handle mutation/start,
  full-duration completion-period charge to the initial actor including
  authenticated failures/denials. Fixed half-open periods, process-reset counters,
  unbounded running-request time overshoot, no reservations or cancellation.
- Exhaustion is explicitly `{status:"quota",value:null}` host control metadata,
  outside `S.Status`, never a technical failure. It obeys the response-size
  ceiling through common bounded control preparation; quota/null (53 bytes) is
  shorter than the fixed certificate/null error required by valid configuration.
- Modular `selected`, `authenticated`, `completed` hooks and injected `Clock`.
  Completion currently follows cleanup/publication before inspection/delivery.
  Future accepted scheduling/persistence adapters must retain that boundary and
  place durable commit before completion; this branch supplies neither feature.

Contract changes: explicit principal bytes prefix private successful authentication
metadata, administrator log observation, opt-in policy receipt/progress extension.
The ordinary eight-law theorem is preserved for ordinary operation and is not
claimed to prove quota accounting or the new host protocol. Actual proof targets
are `Messages.principal_is_authenticated_id` and
`Messages.authentication_binds_principal_and_instance` in `src/Messages.bend`.
Both refer to actual private output construction used by stage compilation.
The Rust/Node/native byte bridge, host hook order, monotonic OS clock and quota
arithmetic remain trusted integration contracts tested below. No final validity
assumption, certificate bypass, or canonical contract modification was added.

Validation so far: `cargo test --locked` passed all 15 unit tests. These include
controlled-clock selection/auth/completion boundaries, exact exhaustion,
completion-period crossing, fresh identity/credential exchanges, authenticated
rejection charging, concurrent already-running tokens/unbounded overshoot,
restart reset, timing-only pass-through, private identity byte transport, CLI
validation, NDJSON escaping and log IO errors. Existing framing/publication/
delivery/worker tests also passed.

The locked official proof and real-service timing run is in progress. Final
commands/results will be recorded after prerequisite integration. New integration
tests exercise actual source/proof binding, state/credential changes, current
identity quotas, authenticated certificate failure charging, denied handle
invalidation, restart reset, timing-only ordinary responses, stderr/file logs,
and terminal framing exclusion. No CPU/performance benchmark has been run.

Costs/limitations: two constant-time clock samples for timing-only service;
quota adds one authentication clock sample and per-period user-map
lookups. Log serialization/output is after the measured interval and can delay
subsequent selections. Elapsed time includes worker/compiler waits and any
intermediate inspector output. Counter memory is per distinct completed principal
within a period; rollover clears it. Log file growth is administrator-managed,
write failures disable the observer without undoing service, and there is no log
fsync guarantee. No counters survive restart. Requests that never complete are
not charged; overshoot has no time bound. Scheduling and persistence integration
await accepted prerequisite hashes; there is no claim of a composed host proof.

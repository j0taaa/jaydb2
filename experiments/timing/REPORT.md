# Timing and quota experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6` (common anchor).
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Accepted preprocessing prerequisite `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`
was merged as `0596bdc` after standalone feature checkpoint `bf32900`.
Accepted scheduling prerequisite `23f7bcb7e8b718288a7cad869215b8acee91b005`
was merged as `9675a22`. `Database::execute` starts timing only on dispatched
Request events, owns the token with the proposal in `ServiceCompletion`, and
`publish_completed` consumes it after publication, before inspector/log/delivery.
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
  Accepted serial queue integration retains that boundary, with no timing on
  terminal framing events. A future accepted persistence adapter must place
  durable commit before completion; this branch currently supplies no durability.

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

Validation so far: `cargo test --locked` passed all 25 unit tests after accepted
serial scheduling integration. `cargo clippy --locked --all-targets -- -D warnings`
passes (two new nested-if findings were corrected). These include
controlled-clock selection/auth/completion boundaries, exact exhaustion,
completion-period crossing, fresh identity/credential exchanges, authenticated
rejection charging, concurrent already-running tokens/unbounded overshoot,
restart reset, timing-only pass-through, private identity byte transport, CLI
validation, NDJSON escaping and log IO errors. Existing framing/publication/
delivery/worker tests also passed.

`make build` passed under the heavy lock. `python3 -B tools/check.py
src/Messages.bend` passed both official checkers, including both new binding laws.
`python3 -B -m unittest tests.service.test_timing -v` passed all four tests in
55.776s on the initial feature binary. These exercise actual source/proof binding,
state/credential changes, current identity quotas, authenticated certificate and
runtime failure charging, denied handle invalidation, restart reset, timing-only
ordinary responses, stderr/file logs, and terminal framing exclusion.

The response-bound correction and subsequent serial queue integration require
the queued rebuild/pipelined native rerun. Full official/default/prepared/native
differential regressions are also queued. Final commands/results will be recorded
when those finish and the final persistence prerequisite is integrated.
No CPU/performance benchmark has been run.

Costs/limitations: two constant-time clock samples for timing-only service;
quota adds one authentication clock sample and per-period user-map
lookups. Log serialization/output is after the measured interval and can delay
subsequent selections. Elapsed time includes worker/compiler waits and any
intermediate inspector output. Counter memory is per distinct completed principal
within a period; rollover clears it. Log file growth is administrator-managed,
write failures disable the observer without undoing service, and there is no log
fsync guarantee. No counters survive restart. Requests that never complete are
not charged; overshoot has no time bound. Serial scheduling is integrated; persistence integration awaits its accepted
prerequisite hash. There is no claim of a composed host proof.

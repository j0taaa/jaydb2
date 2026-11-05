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
  merged as `5bb4f20`; required full-uint64 state-limit correction
  `6c6e494c081b3332d244900b14a6a9581249a4aa`, merged as `03c6b81`.

No unaccepted sibling changes were incorporated. The pinned official tools are
an immutable `.tools` symlink to `/home/jota/projects/jaydb2/.tools`. Build,
output, fault-binary, temporary and state paths are worktree-local for final
validation. No push, PR, deployment or main merge was performed.

## Supported behavior

Actual implementation and complete CLI/accounting/contract examples are in
[`SERVICE_TIMING.md`](../../tools/service/SERVICE_TIMING.md).

```
mkdir -p build
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

Completed checks (all passed unless the corrected test oracle is noted):

- `cargo test --locked`: 31 combined host/clock/scheduling/storage/model tests
  passed on the final integrated source, including the full-u64 state-limit
  boundary and controlled-clock use of the actual durable-ready callback.
- `cargo clippy --locked --all-targets -- -D warnings`: passed. Two timing
  nested-if findings were corrected before this pass.
- `make build`: passed under the shared lock on initial and final integrated
  production source `03c6b8129215647ab758c52d057e4fe1af1ea3b0`.
- `python3 -B tools/check.py src/Messages.bend`: both official checkers passed
  both new identity/instance binding laws.
- `python3 -B -m unittest tests.service.test_timing -v`: all four initial
  real-worker tests passed in 55.776s before response-bound/queue/storage
  integration. Final coverage below supersedes that initial binary.

Final integrated focused evidence (`.build/timing/focused-checks.log`): release
build, all 31 host/model tests, strict clippy, and both real queued-identity/quota
and durable-reopen/reset timing cases passed (two native tests in 34.627s).
Both actual fatal subcases after replacement and after RAM publication passed.
The initial fault method failed only because its before-replace hook was expected
to be rollback-safe; the accepted storage adapter conservatively marks every
error from the replace primitive uncertain, including that hook. Production code
was preserved. The test now separately covers after-file-sync known rollback,
before-replace fatal/old image, after-replace fatal/new image and after-publication
fatal/new image. The corrected fault-only recheck passed all four subcases in
51.062s (`.build/timing/fault-recheck.log`). It ran the test now committed at
`dbe5e15f8f268fafdd74abfe7422c0a20dac93a4` against the feature-built binary
from frozen production source `03c6b8129215647ab758c52d057e4fe1af1ea3b0`.
No production code changed to accommodate the corrected oracle.

All focused native runs use `flock /tmp/jaydb2-experiments-heavy.lock`, with
`TMPDIR="$PWD/.build/timing/tmp"`; the fault binary is local at
`.build/timing/fault/release/jaydb2` with `storage-fault-injection` enabled.
All obsolete broad/redundant jobs were canceled while their lock processes had
no child; no running test was interrupted. Completed evidence is preserved.

The focused commands inside that lock were:

```
make build
cargo test --locked
cargo clippy --locked --all-targets -- -D warnings
python3 -B -m unittest tests.service.test_timing.TimingTests.test_completion_charge_tracks_actor_across_credential_exchange tests.service.test_timing.TimingTests.test_durable_publication_and_quota_reset_after_same_binary_reopen -v
cargo build --locked --release --features storage-fault-injection --target-dir .build/timing/fault
JAYDB_PERSISTENCE_BINARY="$PWD/.build/timing/fault/release/jaydb2" python3 -B -m unittest tests.service.test_timing_persistence -v
```

The final narrow gate passed on the same frozen production source, with tests
and docs from `dbe5e15f8f268fafdd74abfe7422c0a20dac93a4`
(`.build/timing/final-binding-default.log`):

```
make verify-contract
python3 -B tools/check.py src/Messages.bend proof/Preprocessing.bend proof/Persistence.bend
python3 -B -m unittest tests.service.test_preprocessing tests.service.test_prepared.PreparedTests.test_reuse_current_identity_state_and_sealed_native_without_admission -v
```

Both official checkers accepted the canonical contract, actual principal/source
binding laws, exact preprocessing equivalence including the new principal prefix,
and the recovery-preservation proof. Both native/default tests passed in 49.394s:
exact principal/code/proof fields (including Unicode and empty IDs), generated
current-context binding, all argument forms, malformed/limit/transport/auth error
precedence, current-state ordinary execution, and default prepared reuse/fresh
identity/sealed-integrity/worker isolation behavior.

`cargo fmt --all -- --check` and `git diff --check` also passed. No additional
production changes followed these checks; the final commit records this report.
The full `make verify`, `make test`, all ordinary/scheduling CLI suites,
library/demo checks and benchmarks were not rerun on the final branch; broader
baselines remain coordinator validation as requested. No admission mock suite
was run, so its conditional accepted SIGKILL realpath harness fix was not needed
or cherry-picked. There are no pending/running timing check jobs.

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

## Independent audit clarification

The audit found that the documentation's unqualified "malformed input" wording
was broader than the implemented policy. Canonical decoding/opcode errors occur
before authentication, keep their precedence and are uncharged. A nonempty
execute/invalidate proof is instead a prepared-field error checked after fresh
authentication and quota policy; it returns `input` when permitted and `quota`
when exhausted. These authenticated attempts are charged. This ordering meets
the policy's rule to charge every authenticated completed attempt.

`tools/service/SERVICE_TIMING.md` now states that distinction explicitly.
No production source or accounting order changed. The new real-service
`TimingTests.test_quota_precedence_distinguishes_canonical_and_authenticated_field_errors`
passed under the shared lock in 11.193 seconds: it checks both prepared opcodes
under exhausted quota, invalid authentication, canonical decoding and opcode
errors, and the permitted nonempty-proof `input` outcome and logged principal.
The first invocation had a missing worktree-local `TMPDIR` and failed before
initialization; creating the local directory resolved that test setup error.


## Independent audit runtime-policy repair

The audit also found inherited `BENDRTS` could request independent early-exit
options despite explicit CPU arguments. `Program.run` now clears it, matching
the GPU branch's existing policy. The accepted shared source change is
`b7e873cb8e3638de23313ff3655d0feedfa2e4e0`; test-only follow-up
`c39bebbd0a9b64380dd10cdeea9112b82b52d5fe` uses one immutable executable
launch fixture. This avoids a write/exec race seen as `ETXTBSY` in an earlier
parallel test run, without production retries or global environment mutation.

Post-repair evidence, using the common heavy lock:

- All **32** Rust host/model tests pass with no ignored tests; strict
  all-target Clippy and formatting checks pass. Evidence:
  `build/audit/runtime-policy-fixture.log`.
- A release rebuild and the real
  `EndToEndTests.test_native_runtime_options_are_owned_by_host` pass
  (**16.256 s**). It starts with inherited `--gpu-build --help`, performs
  an admitted ordinary credential update, prepares a universal program and
  executes it with current credentials.
- Validated `server/main.rs` SHA-256:
  `32f2fd569c9413d1cc6d4bd79230262d1205c63514e619bbc7cf987ad8f47129`. Later report-only edits do not change that source.

This is a process-runtime boundary repair. The Bend admission/proof functions
and canonical request/state/response formats are unchanged; their previous
proof results are retained without claiming another full aggregate rerun.
The previous performance measurements, if any, remain measurements of their
recorded revisions; no benchmark was repeated for this repair.

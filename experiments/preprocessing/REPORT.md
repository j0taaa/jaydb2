# Native request preprocessing

Base: `5925c57febd978d44fa24000233647a59e7898a6` (common experiment anchor).
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
No experiment prerequisites or sibling commits are used.

## Implemented scope

The actual Rust request route now launches the existing native authenticator
directly. Its unchanged `Input.analyze` decodes the private transport, state and
canonical request before authenticating. The prior decode-only child repeated
this same decoding and discarded the result. Initialization also stops building
the unused decoder. The staging module retains its decode-only capability for
the differential test; production initialization and dispatch never use it.

The change applies to ordinary submissions and prepare/execute/invalidate
controls. No new CLI flag or public protocol is needed. Example commands
(use one live server session for handles):

```sh
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1
python3 tools/client.py --code examples/access/Client.bend \
  --proof examples/access/ClientProof.bend --credential alice-token \
  --arguments '"alice-new"'
```

The execution entry and prepared resolver are unchanged. Each execution still
analyzes the actual current state, credential and arguments in a fresh process.
No context cache, persistent worker, retry or additional state storage exists.
Admission still binds exact source/proof/args/configuration/dependencies, and
prepared artifacts retain their integrity checks and no-Node reuse path.
Private state remains in RAM/pipes; public compilation directories receive no
private snapshot or credential. Both process exit and cleanup still precede
ordinary publication. The host-facing diff removes one field, one load and one
preprocessing call, leaving later lifecycle integration local to that call site.

## Contracts and proof

No canonical limit, administrator law, admission contract or logical protocol
changes. Full extension bytes count against the host's message limit before
prefix removal. Malformed requests precede authentication; invalid credentials
precede certificate admission and handle/proof-field validation. Unknown
opcodes remain input errors. State/response limits and prepared receipts retain
their existing behavior. The frozen environment hash changes naturally because
it binds the controller and staging source.

`proof/Preprocessing.bend` is imported by `proof/VERIFY.bend`.
`gate_preserves_exact_output` compares the removed decode gate's pure result
against `Messages.authentication(Input.authenticate_pre(input))`, for every
`Input.PreAuthentication` constructor. `single_pass_preserves_exact_output`
specializes that equality to actual `Input.decode`/`Input.analyze`, for all
bytes/schemas/limits without successful-input or final-validity premises.
It covers exact metadata/error bytes, including private transport errors.
The negative fixture `PreprocessingAuthenticationFirst.bend` deliberately
misclassifies malformed input as authentication failure.

These theorems establish pure route equivalence, not OS/compiler correctness.
The bridge still assumes the same frozen official programs, exact copied
packet/snapshot and artifact integrity. Rust/Node/C, the official compiler and
runtime, and the OS remain trusted as documented by the existing service
contract. Existing authentication, admission and prepared proofs retain their
scope. Removal of an unnecessary child intentionally removes its possible
physical launch/crash failure; no equivalence of arbitrary OS failures is claimed.

## Checks run

All heavy commands use `flock /tmp/jaydb2-experiments-heavy.lock`. Builds,
logs and temporary service state are local to this worktree. `.tools` is an
ignored symlink to the immutable shared official toolchain.

Passed:

* `cargo test --locked`: 7 host tests.
* `cargo build --locked --release`, `cargo fmt --check`, `git diff --check`.
* `flock ... env TMPDIR="$PWD/build/preprocessing/tmp" python3 -B -m unittest
  tests.service.test_prepared.PreparedTests.test_reuse_current_identity_state_and_sealed_native_without_admission -v`:
  real preparation, changing users/args/credentials, refusal and native failure
  rollback, source/dependency/executable/tooling tampering, original input
  mutation, foreign/invalidated handles and causal no-Node execution gate.
  Added ordinary/control malformed-input vs credential/proof/handle precedence
  assertions, and asserted that no decoder was compiled.
* `flock ... env TMPDIR="$PWD/build/preprocessing/tmp"
  JAYDB_PREPROCESS_TRACE="$PWD/build/preprocessing/launches.trace"
  python3 -B -m unittest tests.service.test_preprocessing -v`: passed (22.521 s).
  Compares exact legacy gate and single-pass native outputs for six successful
  context/argument combinations, invalid credentials with bad source/proof,
  eleven malformed inputs, exact/excess message ceilings, and five invalid
  private transports/state boundaries. Exercises real host admission, success,
  stale credentials, refusal, handle controls and full prefixed message limits.
* `flock ... python3 -B tools/check.py proof/Preprocessing.bend`: both pinned
  official primary checker (`--check-only`) and BendTT (`--verdict`) passed.
* `flock ... env TMPDIR="$PWD/build/preprocessing/tmp"
  make verify-contract verify`: all contract/implementation/proof-test/library
  aggregates passed both official checkers. All seven causal negative fixtures
  failed as expected, including `PreprocessingAuthenticationFirst.bend`.
* `flock ... env TMPDIR="$PWD/build/preprocessing/tmp" make test`: all 15
  admission/verifier tests, 10 native runtime tests, 7 Rust host tests and 6
  real service integration tests passed. The full integration suite took
  151.589 s; this includes repeated admission/compilation, not a latency result.
* `make build` (via `make test-demo-web`): release build passed.
* `flock /tmp/jaydb2-experiments-heavy.lock env TMPDIR="$PWD/build"
  make test-demo-web`: all 5 HTTP demo tests passed in 144.988 s. This covers
  custom programs/proofs and live inspection, HTTP boundaries, publication and
  rollback, session isolation, repeated reset, and startup-failure recovery.
  The actual command exited 0; output is in
  `build/preprocessing/demo-final.log`. Completed proof/core/native checks
  were reused rather than rerun.

The first broader command was `flock ... env TMPDIR=... make verify-contract
verify test test-demo-web`. It completed the above proof checks, then stopped
with 14/15 admission tests passing: the existing kernel-crash injector compared
an unresolved `.tools` path against the actual resolved executable and missed
the subprocess when using the authorized `.tools` symlink. The test now uses
`realpathSync` and explicitly asserts interception. Production admission and
the pinned toolchain are unchanged. Checks resumed with `make test
test-demo-web`, without repeating the expensive completed proof aggregates.
That run completed `make test`, then the demo suite failed before database
startup because the selected deeply nested local TMPDIR produced Unix socket
paths over Linux's AF_UNIX path limit. A direct local bind/connect smoke check
passed with `TMPDIR="$PWD/build"` (100-byte socket path). A demo-only rerun
was queued, then cancelled while confirmed still waiting, at the user's explicit
coordination request to prioritize the first Bend-host/concurrency/idempotency
native gates. No running test was interrupted. Once the priority gates had
their turn, the user authorized the single deferred demo rerun using the short
local TMPDIR. It passed as recorded above. No production code change was needed
for the temporary-path setup error, and no validation remains deferred or queued
by this thread.

The new native differential test is included in `make test-integration`.
Optional `JAYDB_PREPROCESS_TRACE` requires Linux `strace`; the test otherwise
uses the same real native/service assertions without a tracing dependency.

## Process cost observations

The traced host differential test executed exactly 1 initialization child,
18 authenticator children and 2 execution children, and zero decoder children.
This is actual `execve` evidence, with `--threads 1`; Node/checker/compiler
subprocesses are excluded from these native request-stage counts. Invalid or
malformed requests never executed client code. The reference decoder runs
outside the traced service and is not counted as service activity.

For a well-formed ordinary/prepared execution reaching a worker, native request
launches decrease from 3 (decode/authenticate/execute) to 2; authenticator-only
attempts and prepare/invalidate controls decrease from 2 to 1. Malformed input
still uses one native child, now the authenticator. Framing rejection uses zero.
Startup compiles two native programs instead of three. These per-route savings
follow from the removed call; the trace verifies the new counts. End-to-end
latency and throughput gains are not measured, and integration test wall time
includes compilation and tracing rather than constituting a benchmark.

## Limitations

The execution worker deliberately repeats decoding/authentication to retain
actual current-input binding. Prepared calls still generate unused public
admission metadata in the authenticator. Compilation dominates ordinary calls;
no cache or specialized handle authenticator is introduced. Requests remain
serial; this branch adds no durability, scheduling, quotas or concurrency.
Official Bend 2.0.39 native representation/failure limits remain in force.


## Independent audit runtime-policy repair

The audit also found inherited `BENDRTS` could request independent early-exit
options despite explicit CPU arguments. `Program.run` now clears it, matching
the GPU branch's existing policy. The accepted shared source change is
`b7e873cb8e3638de23313ff3655d0feedfa2e4e0`; test-only follow-up
`c39bebbd0a9b64380dd10cdeea9112b82b52d5fe` uses one immutable executable
launch fixture. This avoids a write/exec race seen as `ETXTBSY` in an earlier
parallel test run, without production retries or global environment mutation.

Post-repair evidence, using the common heavy lock:

- All **8** Rust host/model tests pass with no ignored tests; strict
  all-target Clippy and formatting checks pass. Evidence:
  `build/audit/runtime-policy-fixture.log`.
- A release rebuild and the real
  `EndToEndTests.test_native_runtime_options_are_owned_by_host` pass
  (**16.274 s**). It starts with inherited `--gpu-build --help`, performs
  an admitted ordinary credential update, prepares a universal program and
  executes it with current credentials.
- Validated `server/main.rs` SHA-256:
  `556ac42ea50cd17255faa6d24cd79c9df7803d131b8ebf8f5f6808dd382fb02d`. Later report-only edits do not change that source.

This is a process-runtime boundary repair. The Bend admission/proof functions
and canonical request/state/response formats are unchanged; their previous
proof results are retained without claiming another full aggregate rerun.
The previous performance measurements, if any, remain measurements of their
recorded revisions; no benchmark was repeated for this repair.

## External-review follow-up: helper cleanup

The inherited `Scope::spawn` setup path could unwind before `Child::wait` and
join a pipe blocked on a still-running helper. `server/capture.rs` now owns the
child inside the scoped closure, uses `Builder::spawn_scoped` for fallible pipe
startup, and kills/reaps on early return or unwind before implicit pipe joins.
The original fatal startup-failure policy is retained after cleanup; no new
public receipt or retry is introduced. Staging freezes this module alongside
the other controller sources. The shared module is byte-identical across the
nine active Rust-host variants. Main and the baseline comparison host remain
unchanged; no experiment branches were merged.

All 11 Rust host/model tests, strict all-target Clippy, formatting and release
build passed on this branch. New tests cover an injected startup error and an
unwind at EACH pipe-thread start, blocked stdin/output, actual child reaping,
and the fatal public capture path. A real ordinary/prepared/current-authentication runtime-policy
regression also passed. No Bend source proof, compiler, checker or runtime
implementation changed, so their earlier proof results remain scoped to their
recorded revisions rather than being relabelled as rerun aggregate evidence.

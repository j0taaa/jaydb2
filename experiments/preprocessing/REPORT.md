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

Passed so far:

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

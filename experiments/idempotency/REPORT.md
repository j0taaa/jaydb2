# Idempotency experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6`.
Original reference: `9b751fab3c7c349ff473a2d11a7133573b6c4df2`.
Accepted integration prerequisites: persistence/preprocessing checkpoint
`83a9f3703345c234fe3b14363e6e14e15cb88b80`, followed by its required
u64-limit boundary fix `6c6e494c081b3332d244900b14a6a9581249a4aa`.
Both exact commits are merged. No new library experiment prerequisite is used;
only this branch's receipt modules and the anchor's task proof foundation are
imported. The later accepted optional library foundation is not required.

Completed and validated. The complete focused gate ran at source head
`65fe3511aa30ff9d221a8f5b102320e2a20e17b9`; the final report-only commit
changes no tested implementation or harness source. All work remains local to
`experiment-idempotency`; no push, deployment, PR or main merge was performed.

## Supported behavior

Ordinary optional `library/Receipts.bend` provides bound input/version/result
lookup, a scalar full-row writer, and explicit operation-specific continuations.
No host admission/publication/authentication behavior is replaced. The actual
voucher application writes a business row and a separate immutable receipt row
in one call. Authenticated principal tables partition request IDs; prefixes
`r:`/`v:` partition receipts/effects. Exact canonical input includes the text
and cancellation flag. Operation `voucher.issue/v1` is stable across instances,
independent of prepared handles. Same input returns the small voucher ID only
after current authorization; changed input refuses. Principal registry access
is prohibited, so IDs cannot be deleted/reused even after retirement.

Explicit `retire` atomically deletes both rows and ends protection. Retention is
unbounded until retirement or the normal state ceiling. The example gate is
self-managed per principal: owners can disable/re-enable their own application
permission; hit and miss both consult its current value. No helper privilege,
receipt lock, arbitrary response cache, retry, cleanup worker or concurrency
protocol is introduced. Only existing scalar columns are used.

Examples and CLI: [application README](../../applications/vouchers/README.md).

```sh
flock /tmp/jaydb2-experiments-heavy.lock make test-idempotency
flock /tmp/jaydb2-experiments-heavy.lock python3 -B applications/vouchers/check.py --restart
```

## Laws, proofs and trust boundary

`ReceiptLaws.Rule` is an administrator-frozen semantic protocol refinement
law template, not a source allowlist. `Reachable`/`At` bind every actual prefix's
working state and operation/effect history to a reference execution.
`Closed`/`Success` require completed reference success before success is allowed.
Stable `State` constructively witnesses provenance from receipt-free initial
application tables through complete reference calls. `extend` proves preservation
by adding the actual transaction to the erased witness. `finalized` and
`finalize_equivalent` connect technical finalization without assuming final
validity. The witness is mathematical proof data; it is neither emitted as
runtime history nor persisted or replayed by the host.

The instantiated reference `Voucher` binds exact canonical input/version/result,
creates effect and receipt together, never rewrites live receipts, and allows
only paired retirement deletion. Its table initialization predicate leaves
registry values abstract; no private state is written to public checking files.
The existing task `Policy`/`Ownership`/`Proofs` foundation separately proves
principal ownership, registry nonaccess and actual per-operation permissions.
`ClientProof.program_safe`, `certify`, `trace`, `publication_cases` and the actual
`Bindings.certificate`/`Bindings.terminates` targets compose these properties at
all prefixes and final publication. Temporary effect/receipt mismatch is
permitted inside the specified path; incomplete paths cannot publish success.

The administrator must freeze a correct operation specification and initial
predicate. Arbitrary specifications do not acquire idempotency merely by using
the template. This is a serial/library extension under the existing host bridge,
not a new serial-host theorem. Native bytes, compiler/checker/runtime fidelity,
fresh authentication, publication, and persistence filesystem/flush assumptions
remain those of the existing contracts and accepted persistence prerequisite.
Storage hashes alone are neither authorization nor law-validity proofs.

## Validation record

The complete command passed (exit 0) at
`65fe3511aa30ff9d221a8f5b102320e2a20e17b9`:

```sh
mkdir -p applications/vouchers/.build/tmp
TMPDIR="$PWD/applications/vouchers/.build/tmp" \
  flock /tmp/jaydb2-experiments-heavy.lock bash -c \
  'make build && python3 -B applications/vouchers/check.py --restart && cargo test --locked && python3 -B tools/check.py proof/Persistence.bend proof/Preprocessing.bend'
```

Actual results:

- `make build` / `cargo build --locked --release`: passed using the pinned
  official toolchain and the merged controller.
- The native harness's flat development application/proof/seed package passed
  official primary `--check-only` and BendTT `--verdict`. The generic universal
  certificate proof is checked here; actual generated `Bindings.certificate`
  and `Bindings.terminates` targets are checked by real request admission.
- `experiments/idempotency/VERIFY.bend`: all eight functional model targets
  passed both checkers. They cover exact hits, version conflict, exact-input
  conflict (with its actual read event), unchanged hit state, real second-write
  `Data.operate` failure and rollback, and state/response-limit rollback.
- `applications/vouchers/check.py --restart`: **43 real framed request checks
  passed**. Each positive admitted program uses official checking/compilation
  and native execution. Covered separate principals using one ID; same-input
  hits; changed text/cancellation conflicts; present permission on hits and
  misses; refusal after both provisional writes; explicit paired retirement
  and ID reuse; empty/delimiter IDs; Unicode/NUL inputs and normalization
  differences; 64/65-scalar ID boundaries;
  fresh authentication; actual state/response/message-limit behavior.
- All five deliberate bad programs returned `certificate`: receipt-only
  forgery, live result mutation, permission bypass, foreign read then refusal,
  and principal deletion. The first two include genuine per-operation ordinary
  ownership proofs and fail specifically at `certify`'s frozen protocol
  binding, beyond mere permission/source mismatch. The harness verified exactly
  five `PRIMARY_CHECK` rejections and at least two `Location: certify` messages;
  follow-up requests confirmed unchanged state.
- The state-limit case verifies absent business data followed by a different
  input's successful issue under the same ID. The response-limit case uses
  a 96-byte response ceiling: the 129-byte success cannot fit, but a conflict
  refusal can. An absent business read plus a second `limit` on changed input
  therefore verifies neither business row nor receipt was published.
- **Real persistence restart passed**: create storage, issue and durably receive
  `v:persist`, terminate, remove private `Seed.bend`, then open with no seed.
  Same-input hit returns the original receipt; changed input conflicts and
  voucher data remains `durable`. An oversized frame terminates the create
  session before selection; reopening verifies no business/receipt was written
  for it and a new small request with that ID succeeds.
- `cargo test --locked`: **13 passed, zero failed/ignored**, including the new
  `largest_logical_limit_still_recovers_a_small_complete_image` test for the
  exact accepted overflow fix, authoritative-image recovery, ownership/fault
  model, fatal no-response behavior and result-ready publication order.
- `tools/check.py proof/Persistence.bend proof/Preprocessing.bend`: both modules
  passed primary and BendTT.
- Bounded cheap primary checks on the new modules and full staged binding
  package, Python byte compilation, and final `git diff --check`: passed.

Two earlier development runs did not complete: one used the stale pre-merge
controller against the new staging protocol (`HOST_JSON: missing decode`);
rebuilding resolved it. Another harness incorrectly attempted a follow-up call
on a connection closed by the specified terminal oversized-frame behavior.
The test now verifies that boundary across durable reopen. These were corrected
before the complete passing frozen-source gate above. A redundant queued
library-only check was cancelled rather than repeating it.

Full canonical/admission/demo/other-library suites and performance benchmarks
were not rerun by this feature gate. The separately accepted prerequisites
retain their own validation records; no GPU feature or unrelated admission-mock
fix was merged. All test/build/state paths are worktree-local, including native
worker and host-unit temporary directories. `.tools` points to the immutable
shared official distribution; no compiler/checker/runtime source was modified.
The ignored local log is `applications/vouchers/.build/final-validation.log`.

## Costs and limitations

A miss executes permission read, receipt-input read and two full-row writes.
A hit executes permission, input, operation and result reads. Retirement executes
one permission read and two deletes. Input is duplicated into the business row
and canonical receipt; total state is subject to the existing canonical ceiling.
The small result is a voucher key (at most 66 Unicode scalars), not an arbitrary
cached response. Default message/state/response limits remain 32768/65536/32768.
Performance is unmeasured; proof/check/compile cost is not a throughput claim.

The supplied app fixes Alice/Bob tables and freezes principal lifetimes; it
provides no principal-registration API, expiry clocks, opaque incarnation IDs,
external effects, mutable vouchers, or arbitrary multi-operation receipts.
Different operations must define their own stable identity, exact encoding,
result/permission policy and certified specification. Protection ends on
retirement; RAM mode ends it at process exit. Persistence mode adds restart
survival only in the accepted exact environment with protected storage. No
process-kill test establishes power-loss or hardware flush correctness.


## Independent audit runtime-policy repair

The audit also found inherited `BENDRTS` could request independent early-exit
options despite explicit CPU arguments. `Program.run` now clears it, matching
the GPU branch's existing policy. The accepted shared source change is
`b7e873cb8e3638de23313ff3655d0feedfa2e4e0`; test-only follow-up
`c39bebbd0a9b64380dd10cdeea9112b82b52d5fe` uses one immutable executable
launch fixture. This avoids a write/exec race seen as `ETXTBSY` in an earlier
parallel test run, without production retries or global environment mutation.

Post-repair evidence, using the common heavy lock:

- All **14** Rust host/model tests pass with no ignored tests; strict
  all-target Clippy and formatting checks pass. Evidence:
  `build/audit/runtime-policy-fixture.log`.
- A release rebuild and the real
  `EndToEndTests.test_native_runtime_options_are_owned_by_host` pass
  (**16.219 s**). It starts with inherited `--gpu-build --help`, performs
  an admitted ordinary credential update, prepares a universal program and
  executes it with current credentials.
- Validated `server/main.rs` SHA-256:
  `958535bc39bbc21f058c86f747348cf49233bbe83cddc1e979850087d7d76709`. Later report-only edits do not change that source.

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

All 17 Rust host/model tests, strict all-target Clippy, formatting and release
build passed on this branch. New tests cover an injected startup error and an
unwind at EACH pipe-thread start, blocked stdin/output, actual child reaping,
and the fatal public capture path. A real ordinary/prepared/current-authentication runtime-policy
regression also passed. No Bend source proof, compiler, checker or runtime
implementation changed, so their earlier proof results remain scoped to their
recorded revisions rather than being relabelled as rerun aggregate evidence.

### Durable commit with no acknowledgement, then retry

`make test-idempotency-recovery` builds an opt-in storage-fault executable and
runs `tests/service/test_receipt_recovery.py`. The final gate passed (74.010 s):
create unarmed, open with the existing after-directory-sync barrier, prepare
the actual voucher program with its universal administrator certificate, send
an issue and a queued second issue, then SIGKILL after durable replacement and
BEFORE any acknowledgement. At the barrier no request workers remain. The
caller receives zero response bytes. The authoritative image contains exactly
the business/receipt pair for the first issue and nothing from the queued one.

The test removes Seed, reopens with the SAME executable/environment, retries
the same ID/input, gets the original result, checks conflicting reuse refuses,
and verifies exact unchanged state. The normal direct fault-binary test setup
uses the same unlimited OS stack as the launcher; no checker fuel changed.

To distinguish a hit from rewriting the same deterministic row, a test-only
native oracle runs the actual `Core.advance` interpreter and `Voucher.program`
on those exact recovered private bytes. The fresh-state positive control
performs one business and one receipt write; the recovered retry and conflict
perform zero of each. This trace replay complements the live restart test; it
is not a live trace emitted by the ordinary service. The literal official C
is compiled unchanged. No production counter, schema extension, host receipt
privilege or retry feature was added.

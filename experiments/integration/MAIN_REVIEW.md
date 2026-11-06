# Main-merge review

## Recommendation

**Recommend merging the repaired integration branch. No unresolved merge blocker
was found after the independent reviews, repairs and completed final gates.**

The tested production source is
`00d973e58217dbb589e4fdd0a48815a623faae9a`; later publication adds only this review,
its evidence and evidence whitespace attributes. The reviewed original `f514530`
had two reproduced runtime defects and a malformed-configuration startup defect;
those are repaired. The final code was not accepted merely because earlier
experiment reports said it passed.

## Independent scope

Seven separate subagent review assignments plus coordinator review covered:

1. Host framing, bounded scheduling, concurrent reads, timing and process ownership.
2. Durability/recovery, authorization, staging and prepared artifact boundaries.
3. All optional library algorithms, contracts and actual application proofs.
4. Proof linkage/nonvacuity, tracked dependency completeness and evidence/oracles.
5. A separate re-review of the proposed fixes and their regression-test causality.
6. Independent confirmation and design review of directory-alias cycle discovery.
7. A separate re-review of the actual cycle patch and its positive/negative tests.

No reviewer treated old reports as sufficient evidence or required the excluded
GPU/Bend-host/quota/migration projects. The original integration record remains
historical, including its original controller hash and benchmark data.

## Repaired findings

### MR-01 — P2: failed observer diagnostics could suppress ordinary responses

`Timing.completed` called `eprintln!` after a sink error. If stderr also failed,
that diagnostic panicked before the observer was disabled. A real CLI probe with
both destinations `/dev/full` exited 101 with no client response; the same request
with timing disabled returned its canonical authentication response and exited 0.
The inherited inspection-error path had the same pattern, including a possible
failure after publication.

The host now has a best-effort diagnostic writer. Timing and inspection disable
the failed observer before using it; ordinary error and terminal diagnostics use
the same writer. New real tests require a durable credential update and its
success response plus the next authentication response despite full timing and
stderr devices. A disconnected inspector with failed stderr must also preserve
both client responses. No logging queue, retry policy or deadline was introduced.

### MR-02 — P2: pipe-thread startup could leave a compiler descendant running

The previous guard killed only the direct child. The Node staging helper can
already have spawned a synchronous compiler/checker using inherited stderr when
a later pipe-thread start fails. A reproduction with that exact stdio inheritance
returned `HOST_PIPE_SETUP` while its descendant remained alive.

All three fallible scoped pipe threads now start before any helper process and
wait on bounded one-shot channels. A thread-start error or unwind drops the
senders and joins the waiters without launching a helper or descendant. A failed
executable spawn also shuts down those waiting threads. Direct-child ownership
after spawn and existing process-group semantics are retained. This avoids a
larger process-supervision system or changing demo/session cleanup behavior.

Tests use an async-signal-safe pre-exec byte sentinel, a successful-launch
positive control, and exact fault-hook prefixes. They prove no helper launch at
all three error/unwind points. Other cases cover failed exec startup, large
binary/stdout/stderr pipes, unsuccessful child input handling, and no queued
exclusive operation after fatal read-worker failure. This is not a claim of
general descendant cancellation after arbitrary external SIGKILL or process abort.

### MR-03 — early private-source guard hardening

The seed guard compared canonical paths but missed filesystem hardlink aliases,
and the reserved `Seed.bend` namespace exception was too broad. The reviewer
reproduced seed bytes entering temporary staging; initialization proof/import
checks rejected the attempted service. No running-service disclosure or accepted
invalid initialization was established. This was not counted as a demonstrated
authorization bypass.

The guard now compares device/inode identity and permits the reserved Seed target
only for private initialization. Fast tests require direct, symlink, hardlink and
transitive aliases, plus a conflicting public Seed namespace, to be rejected
before any public staging/compiler invocation. No application law was weakened.

### MR-04 — startup robustness: aliased import cycles exhausted the loader

The loader memoized logical module names. A directory symlink back to the
configuration directory let a self-import generate `again/again/...` names
without revisiting a logical target, indefinitely expanding discovery before
preflight. A bounded scratch probe exhausted the JavaScript heap. This is a
malformed trusted-administrator configuration problem, not a valid admitted
request or demonstrated authorization bypass.

Discovery now carries branch-local linked ancestor trails of canonical realpaths
and rejects a repeated ancestor with `IMPORT_CYCLE` before staging. It does not
use a global inode visited set: shared diamonds and finite hardlink-relative
resolution chains remain legal. Four negative cycle cases require exact early
rejection; positive compiler-mocked controls must reach one compilation attempt
and preserve every expected public module byte. The actual patch was independently
reviewed and all four staging tests passed separately.

The loader change was deliberately deferred until the active durable-reopen
suite completed, so no test changed its frozen environment mid-restart. Final
native/application/recovery/demo gates were then rerun on the last loader source.
The general proof inputs and all `.bend` files are byte-identical throughout;
the completed dual-checker aggregate result applies to those unchanged inputs.

Minor documentation drift about prepared operations and persistence was also
corrected. A separate reviewer checked the repairs, including channel drop order,
process-group compatibility, diagnostic handling and causal tests; no blocker
remained in that review.

## Additional independent challenges

- Fresh literal official C passed 98,305 arithmetic/order cases over 19,661
  operand pairs, emphasizing signed limits, carry/overflow thresholds, divisors,
  powers and both operand orders.
- 2,025 composite-key cases passed an independent encoder/parser with delimiter
  mutations, empty components, NUL, combining Unicode, non-BMP and maximum scalar.
- The proof/evidence audit traced 208 tracked modules and 1,817 import edges,
  found no untracked direct proof dependencies, checked 19 evidence hashes and
  11 exact-tree publication mappings, and verified 756 source-file hashes.
- It independently recomputed all 512 original benchmark checksums and statistics.
  Those results remain historical; a new chosen-executable/fresh-build-equal
  comparison is required below for the repaired controller.

The actual operation/Core bridge and whole-continuation read-only proof were
reviewed. Recovery validity rests on protected certified publication origin and
exact bytes, not on checksums. General mathematical signed mul/div correctness,
arbitrary application invariant synthesis and a complete Rust/OS refinement proof
remain outside the documented claims; no such result was fabricated or assumed.

## Final candidate validation

All commands below completed successfully under the shared heavy-work lock,
with unlimited soft stack and a short private TMPDIR where needed:

- At `3559750`: `make build verify-integration test test-library
  test-feature-integration test-recovery-integration test-demo-web`, then strict
  Clippy and formatting. Both official modes accepted the general, contract,
  library and receipt aggregates, with all eight aggregate negative controls.
- At final source `00d973e`: `make build test test-library
  test-feature-integration test-recovery-integration test-demo-web`, then strict
  Clippy and formatting. This passed 21 admission/verifier, 10 native runtime,
  43 Rust, 19 real service, nine recovery and five demo tests. Actual task, index
  and receipt application roots and their negative controls passed both official
  modes. The index durable session checked 25 requests; voucher flows checked
  43. Native library checks covered 1,980 signed64, 1,980 collection and 250
  variable-length full-content cases in unchanged official C.
- A source-only Git export of `00d973e` freshly built and passed all four staging
  tests and two real service tests for host-owned runtime options, access-law
  enforcement and failed-child rollback. It had no `.git` or ignored generated
  files; only the immutable pinned `.tools` distribution was linked.
- The final paired read benchmark freshly built the selected root and required
  exact SHA-256 equality with the chosen controller. All 256 responses matched
  independent expected results. It used two physical cores and a fixed total
  native-thread budget, one warmup and seven measured paired rounds for each
  tiny/heavier runtime-input workload. This supports retaining optional CPU read
  batching for the measured use; it does not establish benefits on large states,
  mixed writes or arbitrary workloads. One reader remains the default.

The normal controller SHA-256 is
`5dc013b9306b632e5ecd4066508c86d56dee0470cfd444fa158ce60dd9e54a36`;
the opt-in storage-fault controller is
`613113561924e58a43fbbc7252e78bcef1fdccf0e0aa8f228cbeb795046a39f3`.
The last repair changes the JS loader, not these Rust bytes. The clean-export
binary has its own build path and is not substituted for the measured controller.

Exact commands, source identities, raw outputs, benchmark samples, failing
reproducers and hashes are in [main-review evidence](evidence/main-review/README.md)
and [validation.json](evidence/main-review/validation.json). The original parent
[evidence](evidence/validation.json) remains historical and unmodified.

No formal obligation, law, checker, compiler, runtime or generated C was weakened
to pass. The report does not turn finite native tests into general mathematical
proofs. All eight input branches remain unchanged ancestors of this candidate;
all 316 files in the original root snapshot still match their original bytes.
Main remains `9b751fab3c7c349ff473a2d11a7133573b6c4df2`; it was not merged.

## Retained boundaries

The candidate remains a Linux x86-64 experimental service using the pinned
unmodified official toolchain. Protected storage, filesystem flush behavior,
trusted OS/compiler/runtime and the operational bridge are explicit assumptions.
The frozen environment binds code/config/controller; it does not byte-pin every
installed system binary. Storage requires its exact environment and executable;
there is no compatibility/migration feature for disposable development data.

Concurrent reads remain opt-in with one reader by default. Large-state/mixed-write
performance, strict physical memory ceilings, CPU quotas, GPU and the Bend host
rewrite are not being smuggled into the merge decision. No main merge, deployment
or PR is part of this review. A positive recommendation is engineering confidence
from the reviewed code and completed evidence, not a proof of absence of all bugs.

# Checked limit words and one canonical state encoding

Task C, 2026-11-12. Pure checked Bend refinements; no new trusted host arithmetic,
toolchain changes, emitted-C rewriting, ABI variant, or publication shortcut.
Raw observations are in [perf-finalization-c.json](perf-finalization-c.json).

## Changes and proof boundary

`src/LimitWords.bend` selects the precomputed canonical `Number64{0, 65536}`
only when the configured Nat ceiling equals 65,536. Every other input retains
the original non-truncating `Bytes.nat64`, including overflow above u64.
The checked guard peels 256 blocks of 256 Nat steps. This still compares the
ceiling unarily, but avoids constructing the reference converter's 65,536
intermediate u64 words. Its soundness and completeness are proved generically
by block count;
`common_guard_hits` checks that 65,536 takes the literal branch.
`convert_equals_reference` proves exact equality for every Nat. Dispatch root
and message ceilings, direct worker ingress and controller root decoding use it.
Dynamic body/encoding lengths and the legacy `Input.parts` reference stay unchanged.

`proof/LimitLiteral.bend` checks the closed literal witness from a small
`nat64(16)` base and the existing checked u64-addition theorem. Explicit
intermediate sums and bounded numeral comparisons keep the witness inside the
pinned checkers' normal stack/fuel limits. Neither checker nor native Nat
representation was changed.

`Requirements.finalize_success_encoded` factors the existing successful
finalizer. `Execution.finish` computes canonical state bytes once, shares them
with the size check, prepares the response and emits those same bytes in Commit.
`finish_equals_reference` proves exact equality to the original Core preparation,
publication and serialization composition for every response, configuration and
state. This includes data/size denials, failed encodings/framing, Keep, and
successful Commit whose root equals its initial root.

`ExecutionAdapter` and `Adapters` apply that equality to the actual stopped step.
`WorkerBridge` and `DispatchBridge` transport the limit equality; the arbitrary
linear oracle remains linear. `ControlClauses` retains exact received-body bounds.
The original quantified propositions remain; the stopped-adapter proof's inputs
are relevant so it can apply the refinement lemma.

`tools/service/stage.mjs` adds one `loadProof('src/LimitWords.bend')` call to
relocate the literal witness's proof closure into admitted Books. Both contract
hash inventories bind the refactored `Requirements.bend`. This is packaging and
source binding, not a trusted replacement computation.

The new causal negatives reject a wrong cached word and success emitting Keep.
Existing `WorkerDecision.keep_iff_non_success` and the reference decision sum
remain intact. Successful reads still emit Commit with the new paired response.

## Measurements

Same i7-11700K machine and pinned Bend 2.0.39; official checkers on admitted
programs; literal official C compiled at the existing `-O2`; one native thread,
volatile storage, last-key reads and alternating last-key updates, no inspector
or profiler. Each condition has one discarded warmup and 100 measured calls.
Timing markers and the administrator timing sink are enabled, as in the baseline.
Cold admission/registration is outside this repeated-call capture.
Canonical root sizes are 898 bytes at 10 rows and 65,503 bytes at 1,105 rows.

The baseline is the committed [diagnosis capture](perf-repeated-diagnosis.json),
at engine source `3f28eb7c69d5da06b2bfe89ce3d720ed6d581acc`. Task parent
`6449e3b` changes only paper diagnostics, with identical engine/proof/tool source.
It was measured at 11:57:39 UTC; the new session began at 2026-11-12T20:55:42Z.
These are separate same-day sessions, not paired or randomized observations.

The executable-source commit is `b8cc3d3d2a93cacb1f30081a1628237f29e7c30d`, with a clean worktree at capture. Subsequent commits add only this evidence report.

| Rows | Operation | Complete call median, before → after (ms) | Worker median, before → after (ms) | After p95 (ms) | n each |
|---:|---|---:|---:|---:|---:|
| 10 | read | 3.894 → 3.303 | 1.945 → 1.584 | 3.436 | 100 |
| 10 | update | 3.915 → 3.296 | 1.952 → 1.581 | 3.404 | 100 |
| 1,105 | read | 37.078 → 31.506 | 26.021 → 20.305 | 34.505 | 100 |
| 1,105 | update | 37.938 → 32.306 | 26.685 → 21.116 | 33.566 | 100 |

These measurements compare the two Bend refinements together. They do not
isolate the two optimizations separately and do not characterize durability or other state
shapes. Inclusive phase medians are reported separately and are not additive.

Four additional native replays verify the admitted executable/C hashes, both
checker receipts, Commit tag, complete canonical root bytes and exact framed
response bytes for read/update at both sizes. The unchanged read roots still
emit Commit. The fixed-clock wrapper restored and verified its original CPU policy.

## Changed files

- [SPECIFICATION.md](../../SPECIFICATION.md)
- [contract.sha256.json](../../contract.sha256.json)
- [contract/Requirements.bend](../../contract/Requirements.bend)
- [native/SIMPLE_RUNTIME.md](../../native/SIMPLE_RUNTIME.md)
- [proof/Adapters.bend](../../proof/Adapters.bend)
- [proof/ControlClauses.bend](../../proof/ControlClauses.bend)
- [proof/DispatchBridge.bend](../../proof/DispatchBridge.bend)
- [proof/ExecutionAdapter.bend](../../proof/ExecutionAdapter.bend)
- [proof/LimitLiteral.bend](../../proof/LimitLiteral.bend)
- [proof/README.md](../../proof/README.md)
- [proof/WorkerBridge.bend](../../proof/WorkerBridge.bend)
- [src/ControlBridge.bend](../../src/ControlBridge.bend)
- [src/Dispatch.bend](../../src/Dispatch.bend)
- [src/Execution.bend](../../src/Execution.bend)
- [src/LimitWords.bend](../../src/LimitWords.bend)
- [src/Worker.bend](../../src/Worker.bend)
- [tests/proof/rejected/EncodingReuseSuccessKeeps.bend](../../tests/proof/rejected/EncodingReuseSuccessKeeps.bend)
- [tests/proof/rejected/LimitWordsWrongLiteral.bend](../../tests/proof/rejected/LimitWordsWrongLiteral.bend)
- [tools/admission/contract.lock.json](../../tools/admission/contract.lock.json)
- [tools/service/stage.mjs](../../tools/service/stage.mjs)

## Trust base

No T1, T2 or T3 duty changes. The old private ABI remains
`1 || frame(root) || response` for Commit and `0 || response` for Keep.
Compiler/runtime preservation and exact host root/response publication remain
the existing trusted obligations. Documentation is updated in `proof/README.md`,
`SPECIFICATION.md` and `native/SIMPLE_RUNTIME.md`.

## Validation

Final validation on the executable source above:

- PASS `make build` (0.2 s).
- PASS `node --test --test-concurrency=1 --test-name-pattern='concrete and prepared staging check the actual worker oracle and bridge proofs' tests/admission/staging.test.mjs` (38.9 s).
- PASS `make verify-contract` (53.3 s).
- PASS `paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_diagnose.py --calls 100` (47.2 s).
- PASS `python3 -B .build/task-c/check_packets.py` (0.1 s).
- PASS `make verify` (697.0 s).
- PASS `make test` (707.3 s).
- PASS `make prepared` (92.5 s).
- PASS `make test-persistence` (698.1 s).
- PASS `uv venv --python /usr/bin/python3 .build/task-c/pytest-venv` (0.0 s).
- PASS `uv pip install --python .build/task-c/pytest-venv/bin/python pytest` (0.0 s).
- PASS `.build/task-c/pytest-venv/bin/python -m pytest paper/test_evidence.py` (15.4 s).
- PASS `python3 -B .build/task-c/check_cpu.py` (0.0 s).

`make test` includes build, the full admission suite, native runtime, Rust host,
service integration and RLS tests. `make verify` covers all maintained proof
roots and the causal negative corpus in both official modes; every one of the
399 negative fixtures is rejected (798 official-mode rejections).

The initial system-Python command `python3 -m pytest paper/test_evidence.py`
failed before collecting tests because pytest was absent. A task-local Python
3.12.3 environment with pytest 9.2.0 supplied the runner; all 30 tests passed.
The failed invocation and successful rerun are recorded separately in the JSON.

Skipped: `make test-accessories-native`, `make test-idempotency-recovery`,
`make smoke`, and `make test-demo-web`. The explicitly permitted minimum and
checks closest to the changed path ran; shared-lock contention made the full
optional sweep impractical in this task session.

All heavy commands hold `/tmp/jaydb2-experiments-heavy.lock` and use
`ulimit -s unlimited`. Timing capture runs through `paper/bench/fixed-clock.sh`.
The initial native attempt was correctly rejected by a stale admission contract
hash; the inventory was updated. Stopped-adapter correspondence now applies
the checked refinement rather than reflexivity. Early literal witnesses
overflowed a checker frontend stack; the final bounded witness and block
comparison pass the unmodified checkers and the default Node admission regression.

## Limits and remaining work

The stretch unchanged-root optimization is deferred: execution retains decoded
state but drops the incoming canonical-byte owner. Reusing those bytes needs
a broader ownership/non-mutation bridge through worker entry and iteration.
This patch changes no host ABI or duty to implement that shortcut.

Whole-state decode, structural validation and one canonical state encoding
remain linear in database size. The added witness closure can increase admission
checking and frozen-artifact integrity work; the complete-call measurements
include the latter. No transient-memory or throughput improvement is claimed.
Combined admission Books must still pass both default checkers after merging
the other performance branches.

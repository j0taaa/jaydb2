# Review fixes for repeated prepared programs

Measured baseline `b8efde8553c6345e126de8d2782d5791ad17bac6` against implementation `f1c3885ab9ece220673f5e7b4c928cddf90a1241`.
Raw captures, checked-source fingerprints and validation logs/hashes are in
[perf-review-fixes.json](perf-review-fixes.json). These fixes restore conservative
recovery and bound speculative worker resources; they make no speed-improvement claim.

| Rows | Prepared operation | Before median ms | After median ms | n before / after |
| ---: | --- | ---: | ---: | ---: |
| 10 | read | 1.131 | 1.141 | 100 / 100 |
| 10 | update | 1.139 | 1.160 | 100 / 100 |
| 1,105 | read | 20.525 | 20.808 | 100 / 100 |
| 1,105 | update | 21.129 | 21.147 | 100 / 100 |

Both runs held the common heavy lock and used `paper/bench/fixed-clock.sh` around
`python3 -B paper/bench/repeated_diagnose.py --calls 100`, after `make build`.
The before run used a Git archive inside `.build/task-e/baseline`; the after run
used this worktree. There was one discarded warmup per condition, one service
session per revision, one native CPU thread, no inspector and volatile storage.
The harness checked every response and both official checker gates admitted each
executed Bend program. No emitted C or pinned toolchain source/runtime was edited.
These are one-session wall-clock observations, not a statistical regression,
throughput, power-loss or fsync claim. Baseline metadata's empty source-list hash
is retained with an explicit caveat in the JSON; an independent exact Git-byte
comparison of the listed source prefixes supplies the actual baseline and after source fingerprints.

The baseline and after wrappers restored CPU policy. Current observed policy:
`powersave`,
`no_turbo=0`.

## Implementation and tests

- `server/storage.rs`, `server/main.rs`: strict nonzero-invalid-slot refusal,
  distinct slot/reason diagnostics, open-only `--repair-invalid-slot`, exclusive
  full-slot evidence file + file fsync + directory fsync before clearing, no v1
  fallback, and explicit format-v1 diagnostic. Fault hooks cover evidence sync
  and clearing boundaries. Ambiguous sequences and incompatible bindings remain
  unrepairable by this flag.
- `server/worker.rs`, `server/main.rs`: eight pooled images process-wide,
  first-come permits released after cleanup, fresh selected spawns above the cap
  or on refill-thread startup failure, MFD_EXEC with EINVAL-only old-kernel
  fallback, required-seal subset check, non-executable/policy-denied refusal,
  and a non-extractable Command wrapper borrowing Image through launch/capture.
- `server/capture.rs`: retained fatal pipe-thread exhaustion policy, with the
  checked-denial transport dependency documented. Existing causal thread-start
  cleanup tests remain; pool cap/release and memfd policy/seal tests were added.
- `tests/service/test_persistence.py`, Rust storage tests: acknowledged-slot
  corruption refuses without byte changes by default, explicit repair saves
  exact evidence and exposes the rollback risk, interrupted writes require
  explicit repair, evidence failures leave snapshot untouched, and v1 stays
  byte-identical in strict and repair modes.
- `tests/proof/rejected/LimitWordsMutatedConvert.bend`,
  `WorkerMutatedPrincipal.bend`, `WorkerMutatedRoute.bend`: actual implementation
  bodies with one checked mutation, claiming the original universal laws.
  `tests/proof/test_proofs.py` verifies source/law binding and only-`false`
  diagnostics in both modes; admission tests run the same six rejection checks.
- `proof/DurableCommit.bend`: strict/operator policy and evidence-sync gates,
  retaining complete existing crash-origin and clearing lemmas.
- Clippy: speculative refill uses `if let`; geometry uses `is_multiple_of`.

## Trusted boundary and documented limits

T1's exact admission/source/Book binding and T2's compiler/runtime preservation
remain required. The clarified T2/T3 acceptance-safety composition is tag 0's
`DispatchBridge.dispatch_denials_equal_prepared_envelope`, tag 4's same handle
lookup plus deterministic re-execution of the same sealed image, and tag 2's
readiness=false fallback. A discarded tag-2 candidate may execute admitted pure
client code that the old path did not run; its universal certificate covers the
observations, it has no host effects/publication capability, and its result is
discarded. Extra work and physical resource/timing effects remain possible.

T3 now explicitly documents strict corruption refusal and operator-authorized
repair, synced evidence before clearing, bounded pool ownership/cleanup, MFD_EXEC
and required seals, and type-enforced image lifetime. See `proof/README.md`
(duties 3–7 and durable assumptions), `SPECIFICATION.md`,
`native/SIMPLE_RUNTIME.md`, `docs/durable-storage.md`,
`tools/service/SIMPLE_SERVICE.md` and `tools/service/PREPARED_PROGRAMS.md`.

Repair can discard the newest acknowledged commit when corruption caused the
invalidity. It is an investigated operator loss decision after an interrupted
commit, never automatic corruption recovery. Linux buffered writes can stop
short on fatal signals, so host-only SIGKILL can also tear a multi-page slot;
deterministic split-write tests do not establish spontaneous tearing or physical
power-loss safety. Evidence is diagnostic, never authoritative, and can accumulate.
Only 4096-byte f_frsize is checked; ext4 durability semantics remain an operator
assumption. Linux errseq can hide an already-reported writeback error from a
new open and leave checksum-valid page-cache-only bytes. After actual sync/EIO
failure: stop, preserve diagnostics, fix storage, reboot, and assess the on-disk
snapshot or backup before reopening. No direct-IO mitigation is claimed.
vm.memfd_noexec=2 may forbid executable images and deliberately fails closed.
The cap bounds pool processes/threads/pipes; registration memfds and total RAM
remain unbounded. Hardened-policy tests simulate rejection/fallback without
changing the machine's global security policy; actual sealed-image execution
and write/grow/truncate/seal rejection run on this kernel.

## Validation

All heavy commands hold the shared lock with unlimited stack; smoke uses FD 9.
Focused checks passed: 58 Rust tests; three implementation mutations rejected
by both official modes (six rejections); `proof/DurableCommit.bend` accepted by
both modes; all-target clippy with `-D warnings`. The clean full verification
run accepted every positive root with complete import coverage, rejected all
408 negative fixtures in both modes (816 rejections), and passed all 48 admission
tests. Persistence passed 11 tests, including the new strict/evidence/v1 cases.
The core run included 17 service integration tests and the native RLS session
with 253 checked responses. Standalone prepared passed two tests; web demo
passed 12. No required suite was skipped.

- `make build`: passed, exit 0
- `make verify-contract verify test-admission`: passed, exit 0
- `make test-persistence`: passed, exit 0
- `make test test-rls`: passed, exit 0
- `make test-accessories-native`: passed, exit 0
- `make test-idempotency-recovery`: passed, exit 0
- `make prepared`: passed, exit 0
- `bash -c 'exec 9>/tmp/jaydb2-experiments-heavy.lock; flock 9; ulimit -s unlimited; export JAYDB_HEAVY_LOCK_FD=9; make smoke'`: passed, exit 0
- `make test-demo-web`: passed, exit 0
- `.build/task-e/pytest-venv/bin/python -m pytest paper/test_evidence.py`: passed, 30 tests, exit 0
- `cargo test --locked`: passed, 58 tests, exit 0
- `cargo clippy --locked --all-targets -- -D warnings`: passed, exit 0
- `python3 -B tests/proof/test_proofs.py --implementation-mutations-only && python3 -B tools/check.py proof/DurableCommit.bend`: passed, exit 0

The paper evidence check uses an isolated pytest environment because system
Python lacks pytest. The original long-running validation driver ended with SIGTERM (143) after
successful proof/admission output. Proof/admission was repeated in a standalone
batch; its post-run wrapper then hit a parse error after being edited while
active. The final proof aggregate used an immutable direct command (proofs-clean) and exited 0.
Remaining suites ran in separately tracked locked batches with actual target
exit status written by the lock-holding child, so an outer tracking-process
interruption could not erase a completed test result. Final
outcomes and the interrupted attempt are recorded in the JSON/log hashes.

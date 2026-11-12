# Prepared calls authenticated by one checked worker

Implementation commit `2fa25dc3c336d6af8dcf89a2069fda64663e67ec` on `t3/prepared-worker-auth` removes the separate authenticator process from candidate-hit prepared executions. All 400 measured after calls returned their expected values and had a prepared-worker marker with no packet-authentication marker. Ordinary admission, preparation, invalidation and uncertain routes retain checked dispatch.

## Fixed-clock measurements

Complete client round trips, milliseconds; 100 measured calls per condition before and after, with one discarded warmup. One service session per condition, volatile storage, threads=1, two users, point access at the last key, no inspector. Administrator timing and opt-in phase markers are enabled on both sides. The CPU is held at performance/no_turbo=1 under the common heavy-work lock; both wrappers restore policy on exit.

| Rows | Operation | Before median ms | After median ms | Reduction |
|---:|---|---:|---:|---:|
| 10 | read | 3.994 | 2.855 | 28.5% |
| 10 | update | 3.950 | 2.838 | 28.1% |
| 1,105 | read | 37.215 | 27.443 | 26.3% |
| 1,105 | update | 37.722 | 28.030 | 25.7% |

The baseline is the untouched production tree from `git archive 6449e3b`, copied inside this worktree. Only its benchmark metadata inventory command was adjusted to find the enclosing Git tree. The raw baseline `dirty` list belongs to that enclosing development worktree; its source fingerprint hashes the archived bytes. The after run is a clean tree at the implementation commit above. Raw samples, exact source/binary/toolchain fingerprints, original and applied frequency settings, commands and p95 values are in [perf-prepared-worker-auth.json](perf-prepared-worker-auth.json).

These are one-machine, warm-cache observations with one independent session per condition. They do not estimate durability/fsync costs or confidence intervals across machines/sessions. The worker still decodes and serializes full state. This change does not incorporate immutable images, worker pooling, limit-word specialization or finalization optimizations from the concurrent tasks.

## Implementation and proofs

- `server/prepared_route.rs` recognizes only a complete canonical prepared-execute envelope. Cursor reads and lengths are checked, loops consume bounded input, and argument nesting above 64 falls back. Unknown/malformed handles, missing artifacts, controls and direct requests use existing checked dispatch. The parser supplies no status or identity.
- `server/main.rs` keeps changes in `propose` and `tentative_prepared`. The complete original body, current root and latest registry are forwarded unchanged. Before decision parsing/publication it requires checked environment and handle equality, artifact binding, and original metadata readiness. Any doubt discards the candidate and retries the original path.
- `src/Messages.bend`, `src/Worker.bend`, `src/WorkerResult.bend` and `tools/service/stage.mjs` add a checked principal/route envelope and retain it beside the unchanged Execution state. The source/proof comparison is shared with the actual oracle guard. The raw decision remains Commit(root,response) or Keep(response); success with an equal root remains Commit.
- `WorkerBridge`, `WorkerDecision`, `CertifiedWorker` and `DispatchBridge` extend exact composition, publication and principal projections. The generated oracle package is closed; the new closed-package corollary supplements the unrestricted existing prepared theorem. No existing theorem is removed or weakened, and all maintained modules remain in the verification roots.
- A checked readiness projection evaluates the original `Messages.authentication` discriminator in the worker. Tag 2 from argument reification/metadata framing requires fallback. This deliberately retains some metadata computation instead of assuming `Generate.instance` cannot fail; it still removes the extra process and full-root pass.
- Native regressions compare all ten tag-0 outcomes in the 15-case ingress matrix with exact worker Keep payloads. Additional cases cover revoked/empty-ID roots, absent/invalidated/malformed/foreign registries, wrong source/proof artifacts and control fallback. Timing tests check principal order, unavailable authenticator paths, phase-marker absence and authenticated worker crashes. Three new causal negatives reject forged principal, route and metadata readiness.

## Trusted base and failure policy

T1 admission/source binding and T2 pinned compiler/runtime preservation are unchanged. Every executed Book still passes both checkers; emitted C is compiled literally, and the pinned toolchain and foreign effects are untouched.

T3 duty 3 now distinguishes tentative artifact routing from authoritative checked selection. It explicitly trusts complete-body/current-root/latest-registry forwarding, parsing and comparing the checked metadata, and fallback before publication. The artifact guard alone is not claimed to establish routing completeness. Duty 5 explicitly makes only the final authoritative result/failure observable; an intermediate tentative failure can be followed by a successful retry. Duty 6 publishes only the accepted checked Commit pair. Physical artifact integrity checks remain unchanged on this branch.

A candidate principal is accepted only with a complete matching ready result. On a crash, malformed result, mismatch or unready metadata, the host retries original checked authentication and preserves that authenticator's principal even if the fallback worker crashes. There is no null-on-authenticated-crash weakening. An authenticator metadata/transport failure still leaves principal null. Authenticated empty IDs remain present, and nonempty raw prepared proofs have no principal. Prepared inspection is delayed until checked validation on the fast path. Retries may run two private workers and can repeat private work; none can publish directly.

These duties and observer policy are documented in `proof/README.md` (T3 3/5/6), `SPECIFICATION.md`, `native/SIMPLE_RUNTIME.md`, `tools/service/SERVICE_TIMING.md` and `tools/service/SIMPLE_SERVICE.md`.

## Validation

All heavy commands run under `flock /tmp/jaydb2-experiments-heavy.lock` with `ulimit -s unlimited`. The full driver releases the lock after each target. Smoke uses the documented nonempty inherited lock FD:

```sh
bash -c 'exec 9>/tmp/jaydb2-experiments-heavy.lock; flock 9; ulimit -s unlimited; export JAYDB_HEAVY_LOCK_FD=9; make smoke'
```

- `make build`: PASS.
- `make verify-contract`: PASS.
- `make verify`: PASS.
- `make test`: PASS.
- `make test-rls`: PASS.
- `make test-accessories-native`: PASS.
- `make test-persistence`: PASS.
- `make test-idempotency-recovery`: PASS.
- `make prepared`: PASS.
- `make smoke`: PASS.
- `make test-demo-web`: PASS.
- `make test-admission`: PASS.
- `python3 -m pytest paper/test_evidence.py`: PASS under the same lock/unlimited-stack wrapper. System Python initially lacked pytest; an isolated `.build/task-b/pytest-env` was created with `uv venv --python /usr/bin/python3` and populated with `uv pip install --python .build/task-b/pytest-env/bin/python pytest`. The successful command prepends that environment's `bin` directory to PATH. No system Python or pinned toolchain was changed.
- Focused both-checker bridge checks, `cargo test --locked prepared_route`, and `python3 -B -m unittest tests.service.test_timing.TimingTests.test_prepared_worker_principal_and_crash_fallback tests.service.test_prepared -v`: PASS.
- `npm ci --prefix clients/typescript` and `npm ci --prefix clients/sql`: PASS under the lock.
- `make verify` includes 400 causal negative fixtures, 800 official-mode rejections, all positive roots and the RLS proof-only gate. None were skipped.

Early development checks found frontend binder/linearity/refinement errors in new proof helpers; they were corrected and the final gates above passed. The first evidence-test invocation could not start because system Python lacked pytest; the isolated-environment retry passed. Attempt history and final log hashes are retained in the JSON. Final read-only CPU verification confirms `powersave` and `intel_pstate/no_turbo=0`.

## Remaining limits

The conservative parser routes deep values and uncertain cases through the old path. Failed candidates can add a second private worker and authentication pass. Some original metadata generation remains for the checked readiness discriminator; full-state transfer/decode/encoding still dominates large calls. T1/T2/T3 remain assumptions rather than a proof of Rust, the operating system or physical execution. This private ABI requires a matching host/worker build; cross-build reopening is already guarded by exact frozen descriptors.

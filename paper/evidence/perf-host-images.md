# Host immutable images and single-use worker pool

Host implementation on `t3/sealed-memfd-worker-pool`, based on `6449e3bc6e682d6236d8324834466b274f587c99` (`perf/repeated-programs`). Measured final tree: `80919ee74e5f87fd79ded755c6669824a99f68b8`. This implements diagnosis recommendations 1 and 5 only. Production Bend, compiler/runtime, literal emitted C and compile flags are unchanged.

## Final measurements

Client-round-trip times in milliseconds. Each cell has **n=300**: one discarded warmup plus 100 measured calls per condition in each of three fresh service sessions. `paper/bench/host_images.py` interleaves baseline/current sessions in order before/after, after/before, before/after under the heavy lock and fixed-clock wrapper (performance governor, no_turbo=1). Storage is volatile; native threads=1; no inspector; timing markers/logging enabled in both variants. The point fixture reads the last key of 10 or 1,105 two-column rows; updates alternate 0/1. Canonical state sizes are 898 and 65,503 bytes. Every response was checked. All raw observations, source/binary fingerprints and command results are in [perf-host-images.json](perf-host-images.json).

| Rows | Prepared operation | Before median | After median | Change | Before p95 | After p95 |
|---:|---|---:|---:|---:|---:|---:|
| 10 | read | 3.990 | 2.153 | -46.0% | 4.320 | 2.251 |
| 10 | update | 3.963 | 2.197 | -44.6% | 4.075 | 2.317 |
| 1,105 | read | 37.204 | 34.983 | -6.0% | 37.983 | 36.004 |
| 1,105 | update | 37.744 | 35.489 | -6.0% | 39.000 | 35.981 |

| Rows | Operation | Before session medians | After session medians |
|---:|---|---|---|
| 10 | read | 3.951, 3.987, 4.032 | 2.144, 2.131, 2.183 |
| 10 | update | 3.958, 3.941, 3.980 | 2.201, 2.192, 2.193 |
| 1,105 | read | 37.081, 37.300, 37.218 | 34.967, 34.960, 35.106 |
| 1,105 | update | 37.747, 37.742, 37.739 | 35.478, 35.458, 35.519 |

These are one-machine warm-page-cache latency observations, with no durability or throughput claim. Fixed clock and a cooperative heavy lock do not isolate every desktop/provider activity. Refill consumes CPU and memory; it hides latency without removing initialization work. The native runtime exposes no readiness handshake: a slot is published after exec, and selection may catch remaining initialization. Phase medians are inclusive and must not be added as independent costs.

An earlier pre-fd-guard run used three before sessions followed by three after sessions. It showed substantial variation and a 7.8% large-update regression, so the final source was remeasured with interleaved order. Those earlier observations are retained in the JSON; no samples were discarded from either run.

| Rows | Operation | Earlier before median | Earlier after median |
|---:|---|---:|---:|
| 10 | read | 3.984 | 2.405 |
| 10 | update | 4.001 | 2.441 |
| 1,105 | read | 37.242 | 36.907 |
| 1,105 | update | 37.878 | 40.833 |

## Implementation and trusted-base changes

- `server/worker.rs` copies each released ELF into an owned CLOEXEC/ALLOW_SEALING memfd, adds WRITE/GROW/SHRINK/SEAL, verifies F_GET_SEALS, then hashes the **sealed contents** against admitted executableSha256. It retains fd numbers above 2 so standard-pipe setup cannot replace the image. `/proc/self/fd/N` execution uses ordinary Command::spawn, preserving posix_spawn. Any sealing/verification failure refuses load. RAII keeps the exact image alive. Initializer/recovery, authenticator, controller, prepared and ordinary workers all use this path.
- `server/main.rs` removes per-run executable hashes and prepared staging-file comparisons. Loaded staging source/C/manifest/ELF files are diagnostic copies. One per-database in-memory snapshot still validates frozen public/runtime files and environment metadata before **every future compilation**; both-checker release remains mandatory. Host-owned compilation storage remains trusted against mutation during validation/use, as at the existing release boundary. No inode/mtime cache or unchecked admission shortcut is introduced.
- Each live prepared image and the authenticator own one idle child and one refill thread, bound to the exact image and runtime policy. The thread has no root, registry, request or credential. Selection alone delivers the current packet and EOF. Every process serves one call, exits and is reaped through the original capture transport before its proposal can publish. Async refill cannot change root/registry or publish. BENDRTS="", telemetry policy and +RTS --threads N --gpu off -RTS are unchanged.
- Dead idle children are reaped and selection falls back to fresh spawn before delivering data. Speculative spawn/status failures do not become a request error or block on administrator stderr; failed slots remain empty. Selected fresh-launch/capture failures follow existing host policy. No request is retried after packet delivery. Invalidation installs the checked registry removal, joins refill and kills/reaps idle children before staging cleanup. Shutdown uses the same RAII cleanup. Existing complete output capture and fatal pipe-thread-startup policy remain unchanged.
- Bounds are per image: one idle child, three pipes, one memfd and one refill thread, plus the selected child while active. Canonical limits do not bound registration count or global RAM. Pool setup thread-allocation failure is an actual host resource error; native process refill failure uses fresh-spawn fallback.
- The integrity duty changes from per-call physical rereads/comparisons to one-time verification plus **trusted kernel memfd seals**, owned-fd identity and exact fd execution. T1 still binds both checker acceptances to compiled/released bytes. T2 still trusts compiler/runtime, dynamic loader, libc/libm, loader configuration and inherited loader variables: old per-call checks did not protect these dynamic dependencies either. Static linking was not adopted; it would broaden compile/manifest policy while the pool already moves startup earlier.

These changes are explicit in `proof/README.md` T2 and T3 duties 4/7, `SPECIFICATION.md` executable-integrity/pool paragraphs, and `native/SIMPLE_RUNTIME.md` identity/failure and host-plumbing sections. README and service/prepared docs reflect the same contract. SERVICE_TIMING.md explicitly keeps completed pre-selection startup outside the request interval while counting remaining work. `tools/service/stage.mjs` includes the new host module in the frozen environment descriptor.

## Reproduction

This worktree only symlinked `.tools` to `/home/jota/projects/jaydb2/.tools`; the pinned installation was never modified. Build an archive of the baseline in `.build/task-a/baseline` and build the current tree, each under the shared lock with unlimited stack. The baseline driver adapts only Git metadata inventory/revision labels for the archive; its source files are unchanged.

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; cd .build/task-a/baseline; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/host_images.py --baseline .build/task-a/baseline --baseline-revision 6449e3bc6e682d6236d8324834466b274f587c99 --calls 100 --sessions 3 --output .build/task-a/paired.json'
```

Final source SHA-256: `df063ddf7898d4a64ac7b405cb3da8787d6c1e14ee55e80a7349473813bd0209`; all three changed sessions use the same binary and source fingerprints. The fixed-clock wrappers restored CPU settings on exit. Final restoration verified all CPU settings; subsequent readback was powersave / no_turbo=0. Restoration and read-only observations are recorded in the JSON.

## Validation

All heavy commands held `/tmp/jaydb2-experiments-heavy.lock` with unlimited stack. Smoke inherited locked fd 9 via JAYDB_HEAVY_LOCK_FD=9. `make test` includes test-admission, test-native, test-host, test-integration and test-rls. Storage/proof/accessory/prepared/smoke/demo suites passed before the final diagnostic-only callback change and isolated unit-test adjustment; the final full `make test` rerun covers final host/native/integration/RLS paths. The benchmark driver was exercised by the final six-session run.

| Command | Recorded result |
|---|---|
| `npm ci --prefix clients/typescript` | PASS |
| `npm ci --prefix clients/sql` | PASS |
| `make build` | PASS |
| `paper/bench/fixed-clock.sh python3 -B -c 'import json; from paper.bench.repeated_diagnose import capture; from pathlib import Path; results=[capture(100) for _ in range(3)]; Path(".build/task-a/after.json").write_text(json.dumps(results,indent=2)+"\n")'` | PASS |
| `make verify-contract` | PASS |
| `make verify` | PASS |
| `make test` | FAIL 2 (corrected below) |
| `make test-accessories-native` | PASS |
| `make test-persistence` | PASS |
| `make test-idempotency-recovery` | PASS |
| `make prepared` | PASS |
| `make smoke` | PASS |
| `make test-demo-web` | PASS |
| `python3 -m pytest paper/test_evidence.py` | FAIL 1 (corrected below) |
| `make test` | FAIL 2 (corrected below) |
| `PYTHONPATH="$PWD/.build/task-a/python" python3 -m pytest paper/test_evidence.py` | PASS |
| `make test` | PASS |
| `paper/bench/fixed-clock.sh python3 -B .build/task-a/final-bench.py` | PASS |

Corrected failures were retained, not hidden:

- The first aggregate test stopped at a shell-script admission sentinel. Replacing that test-only sentinel with ELF preserves its positive/negative release controls under the deliberately ELF-only host.
- The next run passed 44 host tests but the EPIPE assertion raced another test fork temporarily inheriting a CLOEXEC reader. The actual idle child had been reaped. Isolating that pipe assertion in a subprocess removes unrelated-reader timing while preserving kill/reap and pipe-closure checks.
- The initial evidence-test command found no pytest installed. pytest 8.3.5 was installed only into `.build/task-a/python` with uv, then the requested module was rerun using PYTHONPATH.

Rust coverage includes hash-mismatch refusal, write/grow/shrink/further-seal refusal, closed-standard-stream fd safety, correct RTS/environment policy, dead/absent idle children, spawn failure, invalidation/shutdown, selected-child pipe-startup failure, and 100 sequential unique-child calls. Native prepared tests corrupt staging ELF/manifest/authenticator/source files while continuing exact-image execution and reject changed shared inputs before future admission. Logs remain under `.build/task-a/`.

## Open risks

Latency remains sensitive to machine activity; report session spread alongside pooled medians and retain the earlier large-update regression. Whole-state native decode/validation/encoding is unchanged. Async refill consumes CPU and extra per-registration resources, with no global resource quota or readiness handshake. Dynamic dependencies, kernel enforcement and host-owned validation/use windows remain trusted. OS scheduling/resource progress and hard-kill cleanup remain outside the source theorems. No new theorem proves physical process isolation, sealing or compiler preservation.

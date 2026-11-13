# Checked private framing (partial task D)

Implementation: `857436f0ea411d81729511140d0b3f2497dd6304`, branch
`t3/single-pass-state-decoder`, based on
`d7382f4146efc012619037494c6e1ef01aaeb724`.
This delivery implements the proved framing step. It does **not** deliver a
specialized decoder from canonical bytes directly to `D.State`.

## Source and proof changes

`src/Transport.bend` retains the previous implementation as
`separate_reference`. The new separator validates octets while cutting and
constructs the first block in order while unwinding, eliminating its reverse
accumulator. It still constructs one first-block list; it is not a zero-copy
root decoder. Header arithmetic, truncation and uint64 behavior remain exact.

Prepared entry is now `Worker.routed_bytes`. Its outer separator validates the
registry prefix and leaves the untouched inner packet to the inner separator.
The entire nested packet receives one framing octet-validation pass rather
than rescanning the complete root/body at the outer boundary. A prefix-only
parse is deliberately not a fully validated packet.

`proof/TransportScan.bend` proves equality to the previous full separator for
**every** U32 list, including non-octets, incomplete headers and truncated blocks.
`proof/Transport.bend` transfers the original framing roundtrip and accepted-byte
reconstruction proofs through that equality. Existing registry byte bridges
retain their statements. `WorkerBridge.routed_bytes_equals_original_packet`
proves the entire new entry equals the original composed worker on every input;
`routed_bytes_lifts_registered` and `CertifiedWorker.checked_routed_prepared`
connect the actual literal entry to the unchanged certified selection/decision.
The generated entry in `tools/service/stage.mjs` uses that function literally.

Two new causal negatives reject non-octets in the first and second blocks.
Native prepared regressions cover incomplete outer/inner headers, maximum
length declarations over physically short inputs, truncated roots and extra
root bytes, requiring the same private inconsistent result. Existing public
request decoding and all its negative fixtures remain intact.

## Trusted base and scope

No new T1/T2/T3 premise, host authority or byte format is introduced. The
framing refinement needs no canonical-root provenance assumption. Current root,
original body, latest registry, source/artifact binding, checked fresh
credential authentication, route/principal/readiness metadata and Commit/Keep
publication retain their existing obligations. `SPECIFICATION.md`,
`proof/README.md`, `native/SIMPLE_RUNTIME.md` and
`tools/service/SIMPLE_SERVICE.md` document the source refinement and literal entry.

The pinned Bend 2.0.39 installation was only symlinked from
`/home/jota/projects/jaydb2/.tools`. The pinned installation, compiler/runtime, compile flags, Rust production code,
finalization and `Bytes.nat64` were not modified. Emitted C was compiled
literally without patching. Every executed worker is an already twice-checked artifact; profiling
uses its literal emitted-C executable. No existing evidence file or manuscript
was edited.

## Baseline diagnosis

The current merged host/authentication base has a measured checked entry of
9.1765 ms (read) / 9.1384 ms (update) at 1,105 rows. Root decode, conversion and
structural validation take 4.0841 / 4.0845 ms inside that entry. At ten rows,
entry is 0.9390 / 0.9387 ms and root work 0.2608 / 0.2607 ms. These are separate
fixed-clock BPF observations, n=30 after one warmup per condition. Entry ends at
the actual compiler-emitted continuation receiving its result, not a C function
return. The profiler discovers that continuation from the unchanged literal C.

The baseline read `perf record` has approximately 14K cycle samples and no lost
samples: term_drop 21.94%, span_fade 9.24%, rfc_wrap 8.73%, byte concatenation
23.91% including its continuation, byte length 3.89%, octet validation 2.99%,
and transport cut 3.95% plus 2.21% in two cut continuations. These are self
samples across a complete worker execution; they cannot be added to inclusive
entry timings. They support the observed list construction/disposal and
repeated-scan cost. This profile uses the admitted worker copied from the
baseline service, through the existing production capture harness.

## Measurement method

Final service observations use `paper/bench/host_images.py` as an unchanged
interleaving driver over `repeated_diagnose.capture`: before/after,
after/before, before/after, three fresh service sessions per variant, one warmup
and 100 measured calls per operation/state size per session (n=300 per cell).
The baseline is an exact Git archive of d7382f4 inside ignored `.build`; only
its metadata inventory/revision labels are adapted by the existing driver.

Both variants use volatile storage, one native thread, no inspector, timing
markers/logging on, the last key of 10 or 1,105 two-column rows, and alternating
0/1 updates. State bytes remain 898 and 65,503. Initialization and preparation
are outside the intervals; each response is checked. The ready single-use pool,
sealed-image policy and authoritative worker authentication are the same on
both sides. Samples are complete client round trips, warm-cache one-machine
observations. No durability or throughput claim is made.

All builds, checkers, suites and measurements hold
`/tmp/jaydb2-experiments-heavy.lock`; each validation target releases its lock.
Final timings and native profiles use `paper/bench/fixed-clock.sh`
(performance/no_turbo=1, restoration trap). The full source/binary/toolchain
fingerprints and raw observations belong in the new JSON evidence file.

The initial diagnostic before/after run has n=100 per cell, one session:
10-row read 1.4832 -> 1.4568 ms; update 1.5076 -> 1.4690 ms;
1,105-row read 25.7560 -> 24.8949 ms; update 26.2974 -> 25.5278 ms.
These preliminary observations are retained separately; final conclusions use
the interleaved observations rather than pooling these temporally separated runs.

## Final interleaved service measurements

Complete client round trips, median milliseconds; n=300 per variant in each row.

| Rows | Operation | Before ms | After ms | Reduction | Before session medians | After session medians |
|---:|---|---:|---:|---:|---|---|
| 10 | read | 1.492 | 1.458 | 2.3% | 1.488, 1.496, 1.496 | 1.457, 1.450, 1.463 |
| 10 | update | 1.508 | 1.472 | 2.4% | 1.508, 1.512, 1.505 | 1.473, 1.457, 1.481 |
| 1,105 | read | 25.764 | 24.902 | 3.3% | 25.808, 25.772, 25.691 | 24.949, 24.835, 24.949 |
| 1,105 | update | 26.315 | 25.496 | 3.1% | 26.379, 26.291, 26.245 | 25.532, 25.441, 25.481 |

All 1,200 measured after calls have a prepared-worker marker and no separate packet-authentication marker. Every expected status/value was checked. All three after sessions use the clean implementation commit above with one identical production-source fingerprint.

## Native entry profile after framing

Fixed-clock BPF observations, n=30 after one warmup. Inclusive regions in milliseconds; separate runs from the service timings.

| Rows | Operation | Entry before | Entry after | Root before | Root after |
|---:|---|---:|---:|---:|---:|
| 10 | read | 0.939 | 0.889 | 0.261 | 0.267 |
| 10 | update | 0.939 | 0.935 | 0.261 | 0.296 |
| 1,105 | read | 9.176 | 8.527 | 4.084 | 5.019 |
| 1,105 | update | 9.138 | 8.501 | 4.085 | 5.053 |

The large entry decreases by about 0.64–0.65 ms in these instrumented observations. The inclusive root region **increases** from about 4.08 to 5.02–5.05 ms. The codec/converter/structure source is unchanged; input-list construction and ownership differ, and the cause of that subregion increase was not isolated. These medians are overlapping regions, not an additive cost decomposition. The direct typed decoder remains unimplemented.

The profiling inputs were independently checked against the admitted C/ELF hashes and both checker-acceptance flags. All eight before/after operation/state-size cases emitted the exact expected Commit root and response, environment, route, principal and match/readiness flags. Their output hashes equal those recorded by every corresponding replay profile. No copied artifact is treated as a new admission.

## Deferred direct typed decoder

`Dispatch.read_root` still uses `Codec.decode` followed by `State.decode`,
including `D.structure`. No wrapper is presented as a direct typed decoder.
Existing `Representation` lemmas prove Value-to-State reconstruction, explicitly
not the byte parser. CodecTrace/CodecRelax retain `Codec.Machine`/`D.Value`
frames, counters, ancestor minimum lengths, name ordering and UTF-8 state. A
new typed byte machine needs a simulation invariant for those frames, or a
canonical-root roundtrip proof with its T3 provenance premise stated explicitly.
A recursive-descent parser also needs a byte-structural termination argument;
recursion on an arbitrary helper-returned remainder does not supply that proof.
That refinement was not completed. This delivery stops at the proved framing
step rather than introducing an unproved fast path. Whole-state decode and
validation therefore remain, together with one state-prefix list construction.

## Validation and limitations

Every requested final command ran. All passed except `make smoke`, which failed at two pre-existing Rust Clippy diagnostics. There are 405 causal negative fixtures and 810 official-mode rejections; all positive roots and maintained import coverage passed. Raw samples, source/binary/toolchain fingerprints, profiling data, command outcomes, failed development attempts and CPU readback are in [perf-checked-entry.json](perf-checked-entry.json).

Development attempts are retained: the first framing proof put a binder match
after a local rewrite; it was split into helpers matching first. The scanner
needed suspended recursive continuations because a live helper cannot call an
unfilled forward definition. Worker equality helpers needed leading closed
configuration clauses and erased oracle parameters; these are binder/erasure
corrections, not additional logical premises. Final focused transport, framing,
worker bridge and certified-entry modules pass both official modes. The first
aggregate verify attempt encountered the earlier oracle annotation and is
retained separately before the final rerun. An initial perf postprocessing
suffix typo was corrected; its valid raw recording was retained, and the fixed
clock wrapper restored policy on that error path too.


| Final validation command | Result |
|---|---|
| `make build` | PASS |
| `make verify-contract` | PASS |
| `make verify` | PASS |
| `make test` | PASS |
| `make test-rls` | PASS |
| `make test-accessories-native` | PASS |
| `make test-persistence` | PASS |
| `make test-idempotency-recovery` | PASS |
| `make prepared` | PASS |
| `make smoke` | FAIL (exit 2) |
| `make test-demo-web` | PASS |
| `make test-admission` | PASS |
| `PATH="$PWD/.build/task-d/pytest-env/bin:$PATH" python3 -m pytest paper/test_evidence.py` | PASS |

Each command held the heavy lock with unlimited stack. Smoke used inherited locked FD 9 with `JAYDB_HEAVY_LOCK_FD=9`; pytest used only the isolated `.build/task-d/pytest-env`. No requested suite was skipped. The earlier failed aggregate attempt and frontend errors remain in the JSON attempt history.

The long-lived validation launcher terminated with signal 15 (reported exit 143) before its first evidence pytest invocation completed. That partial output is retained separately; the final table records the completed standalone retry, not the interrupted attempt.

Smoke passed its accessory tests, 53 Rust host tests and formatting check, then failed `cargo clippy --locked --all-targets -- -D warnings` with Rust/Clippy 1.98.0: `single_match` at `server/worker.rs:135` and `manual_is_multiple_of` at `server/storage.rs:494`. The exact baseline archive reproduces both diagnostics (cargo exit 101). Both Rust files are byte-for-byte identical to d7382f4; their SHA-256 hashes and both command outputs are retained in the JSON. This entry/framing delivery leaves that unrelated baseline lint failure unresolved and does not suppress it.

Final CPU readback, recorded under the heavy lock, confirms powersave governors and intel_pstate/no_turbo=0. The exact settings/timestamp are retained in the JSON.

## Reproduction

```sh
mkdir -p .build/task-d/baseline-src
git archive d7382f4146efc012619037494c6e1ef01aaeb724 | tar -x -C .build/task-d/baseline-src
ln -s "$PWD/.tools" .build/task-d/baseline-src/.tools
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make -C .build/task-d/baseline-src build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/host_images.py --baseline .build/task-d/baseline-src --baseline-revision d7382f4146efc012619037494c6e1ef01aaeb724 --calls 100 --sessions 3 --output .build/task-d/paired.json'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/checked_entry_profile.py .build/paper-bench/repeated .build/task-d/after-profile --calls 30'
```

Use an empty baseline directory; the archive build shares the pinned `.tools`.
`repeated_diagnose.capture` produces its admitted artifacts and canonical
profile inputs. The scratch `repeated-host` package is built from the unchanged
maintained Rust harness with the pinned dependencies documented in
perf-repeated-diagnosis.md; `paper/bench/repeated_replay.py` bootstraps that
package (run it under the heavy lock and fixed-clock wrapper). Profiles use copies of those already admitted
artifacts; copying is not admission.

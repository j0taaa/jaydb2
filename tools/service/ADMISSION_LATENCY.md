# Admission/compilation latency follow-up

Branch: `t3/reduce-admission-latency`; baseline: `ff96188`.

The service now overlaps the original BendTT executable with official C
emission and Clang. Primary checking and official Safe translation remain
sequential: Safe consumes the primary checker's elaborated `Def.e` trees.
Ordinary workers retain `-O0`; preparation/startup workers retain `-O2`.
There is no checker-verdict cache, changed checker/compiler/runtime, source
rewrite, or long-lived worker. Each successful request still launches a fresh
native process through the existing host.

## Binding and release invariant

1. Preflight snapshots the complete authorized graph and exact foreign C.
   Source/target/purity audits and the official primary checker run unchanged.
2. A semantic seal records original declarations, including checked runtime
   bodies. Official Safe fixes the complete, hashed BendTT payload from that
   private Book. The original pinned BendTT process starts on that payload.
3. The seal is checked immediately before the original C emitter receives the
   same Book object. No submission file is reread. The foreign C snapshot is
   validated before emission. This retains T1's exact checked-Book binding.
4. The official emitter mutates its Book under the existing T2 compiler
   preservation assumption. Its resulting private state receives a second
   seal, which must still match when admission returns. This second seal does
   not assert that the transformed compiler state was separately type-checked.
5. Clang may build the emitted C while BendTT runs. The C bytes must remain unchanged
   during native compilation. C/executable hashes are recorded
   provisionally and verified again after checking/building finish.
6. Both child processes are reaped before a successful admission handle, C
   report, native receipt, or program path is released. Every check must have
   succeeded. A checker failure wins over a simultaneous native-build failure.
   The service removes provisional files on error; no speculative worker is
   loaded or executed. The separate pure check still determines certificate
   rejection versus host failure, preserving wire statuses and publication.
7. Staging verifies the C/native hashes before returning the artifact path.
   Existing Rust artifact validation and fresh-worker execution remain intact.

`compileSubmission`/`compileKernel` are trusted host builder APIs. Their callback
receives provisional C and may compile it, but must never execute the worker or
publish an artifact receipt. Only their successful return authorizes release.
The existing non-speculative admission APIs continue to work; `emitC` now also
checks its stored seal before returning emitted bytes.

The T1 text in `proof/README.md`, admission/verifier guides, and
`SIMPLE_SERVICE.md` describe these boundaries. No Bend theorem or additional
checker-soundness assumption is introduced. Reviewers should focus on the
pre-emission seal, the T2 transition to the second seal, failure precedence,
process reaping, and the receipt/path release boundary.

## Measurement protocol

Each program uses one fresh volatile service with one native worker thread.
Ordinary requests and preparations each have one excluded warmup followed by
ten measured operations. Programs/arguments/assertions reuse `paper/bench/fixtures.py` and
`paper/bench/run.py`: the ten-row trivial read, indexed `set`, and voucher
`issue`. Voucher requests use distinct receipt IDs; indexed writes alternate
their Boolean value. Every output is checked. Preparations retain their live
handles, identically before/after; prepared execution is outside this test.

The existing fixed-clock wrapper applies performance governor/EPP on every
CPU, disables turbo, and restores/verifies its saved policy on exit. Machine:
Intel i7-11700K, nominal 3.6 GHz, 16 logical CPUs, no CPU pinning. Statistics are
median [Q1, Q3], inclusive quartiles, without outlier removal. Startup and
warmups are excluded. These single-session comparisons establish the measured
latency change, rather than a multi-session confidence interval or a general
performance claim.

Run from the version to measure (the baseline used the same harness body in an
ignored script):

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B tools/service/bench-latency.py before'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B tools/service/bench-latency.py after'
```

Raw observations, checked outputs, phase spans, commit/dirty state, tool hashes,
CPU observations and engine fingerprints are under ignored
`.build/admission-latency/{before,after}.json`. The committed thesis evidence
and paper sources are unchanged.

| Program / operation | Before (s) | After (s) | Median reduction |
|---|---:|---:|---:|
| Read / ordinary | 5.734 [5.696, 5.776] | 4.937 [4.908, 4.972] | 13.9% |
| Read / registration | 7.534 [7.515, 7.564] | 6.732 [6.703, 6.752] | 10.6% |
| Indexed / ordinary | 10.026 [10.011, 10.042] | 8.839 [8.829, 8.866] | 11.8% |
| Indexed / registration | 12.742 [12.711, 12.749] | 11.569 [11.481, 11.585] | 9.2% |
| Voucher / ordinary | 10.342 [10.309, 10.522] | 9.097 [9.073, 9.190] | 12.0% |
| Voucher / registration | 12.213 [12.132, 12.294] | 10.917 [10.892, 10.936] | 10.6% |

Ten observations per cell. The baseline Rust executable SHA-256 equals the
after executable SHA-256; only the Node admission/compilation pipeline changes.
Exact metadata and raw-file hashes are in `.build/admission-latency/summary.json`.

`bendtt_translate_check` now overlaps C emission/native compilation. Its span
ends when Node observes kernel completion; synchronous C emission can delay
that observation. Do not sum overlapping spans or use the old serial phase
subtraction to infer an exclusive remainder. `admission_total` is still the
inclusive admission/build wall time. No claimed result depends on adding
phase durations.

## Validation

All required targets passed with the common heavy-work lock and an unlimited
stack. `make build` ran first.

| Command | Exit |
|---|---:|
| `make verify-contract` | 0 |
| `make verify` | 0 |
| `make test` | 0 |
| `make test-accessories-native` | 0 |
| `make test-persistence` | 0 |
| `make test-idempotency-recovery` | 0 |
| `make prepared` | 0 |
| `make smoke` | 0 |
| `make test-demo-web` | 0 |

The final `make test` rerun includes 42 admission/verifier tests, 36 Rust unit
tests, the native runtime checks, and 16 service integration tests. Full proof
verification checks 373 negative fixtures in both official modes (746 expected
rejections), alongside the positive roots and maintained import coverage.

Logs and gate results are in `.build/admission-latency/validation/`; the final
aggregate rerun is `test-final.log` with `test-final-result.json` one level up.
The separate final focused run passed all 16 tests (`focused-final.log`).

For `make smoke`, its nested `flock 9` reused the already-held outer lock to
avoid locking against itself. All smoke checks ran unchanged.

The focused regressions cover successful literal C behavior, rejection of every
thrown builder value (including falsy primitives), primary rejection
before building, negative concurrent BendTT verdicts, simultaneous checker/
builder failure precedence, build failure, Book mutation before emission,
during the builder callback and after ordinary admission, and kernel spawn
failure/cleanup. A real-service
fault test waits for actual Clang completion before refusing the kernel check;
no receipt may exist at that point, and an execution side-effect sentinel must
remain absent. A successful-check control launches that same sentinel, proving
that it detects execution. Existing seal/source-binding tests remain enabled.

Final independent CPU verification confirmed all 16 governors are `powersave`,
all 16 EPP values are `balance_performance`, and `intel_pstate/no_turbo=0`.
The fixed-clock wrappers restored and verified their saved settings on exit;
the final observation is `.build/admission-latency/cpu-restoration.json`.

An earlier candidate measurement is retained under
`.build/admission-latency/initial-after.{json,log}`. Review then hardened the
new builder API's rejection of falsy thrown values. The final after dataset is
remeasured on that final implementation; no sample is selected by latency.

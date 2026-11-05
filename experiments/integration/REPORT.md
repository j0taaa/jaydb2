# Curated integration experiment

## Decision and scope

This branch combines baseline tooling, preprocessing, persistence, optional
library helpers, scheduling, simple administrator timing, certified CPU read
batching and ordinary-table idempotency. `SOURCES.json` records the exact eight
accepted branch heads. They remain ancestors of the integration branch.

Excluded: GPU execution, the Bend controller replacement, quota enforcement,
an accelerated nonunique index layout, migrations and cross-build compatibility.
`Index.scan_equal` remains a deliberately named ordinary full scan, useful for
explicit derived-table consistency examples. Unique claims/lookups remain
optional. The index performance decision and its historical evidence are in
`../library/index_benchmark/README.md`.

Execution remains serial by default (`--read-workers 1`). Parallel reads are
opt-in; writes, ordinary submissions, unknown programs and prepared controls
remain exclusive. The fixed-budget measurements below support retaining this
option on the experiment branch, without choosing a concurrent default or
claiming a benefit for every workload.

`main` and all individual experiment branch heads are unchanged. The original
uncommitted root-checkout work is preserved. This branch is an integration
candidate, with no deployment, main merge or pull request.

## Integration changes

The timing experiment's private authentication success output includes an
explicit length-delimited principal before code/proof/instance metadata. Both
the exclusive and concurrent parsers now consume it. Identity is obtained from
the authenticator's actual context, never parsed from source or cached across
earlier writes. The existing Messages principal/instance laws are retained.

The quota module, quota flags and denial receipts are removed. A small
`server/timing.rs` observer owns monotonic attempt tokens and a shared optional
NDJSON sink. For exclusive requests the completion hook follows durable commit
and RAM publication, before final inspection and delivery. Fatal uncertainty
records a completion once and still stops without a response. Each read stamps
its own completion within its worker after cleanup and proposal checks; a
mutex serializes administrator log bytes after the elapsed time was sampled.
Out-of-order completions and active reads drained after delivery failure are
therefore measured independently of FIFO emission.

Current subprocess cleanup, runtime-option sanitization, storage-limit and
queue fixes are retained. `server/capture.rs` is the accepted guarded/fallible
pipe-thread implementation. Source freezing covers it and the timing module.
No pinned compiler, checker, runtime or emitted C was modified.

Actual combined testing exposed one packaging error: the receipt example
copies the task application's shared proof module, which now imports the
optional library's `Laws`, `Query` and `Action` modules. Its staging helper now
copies those exact dependencies as well. No application law or certificate was
weakened to fix this failure.

Independent source review found no remaining substantive implementation issue.
It caught a documentation mismatch, now corrected: only the batching path
enabled by `read-workers > 1` avoids rewriting an already durable unchanged
root. Default one-worker serial requests still persist successful proposals,
including unchanged reads. No new optimization is claimed there.

## Contracts and proof boundaries

All three canonical limits, ordinary response bytes, administrator-law access
requirements, fresh authentication and exact source/proof/artifact binding
remain intact. Whole-program read-only certification is independent of the
normal universal administrator certificate. It covers every continuation;
unchanged successful state is an additional defense, not the admission rule.

The general aggregate reaches the serial service, preprocessing equivalence,
persistence recovery composition and heterogeneous read-batch/Core/authentication
proofs. The optional library aggregate includes its strengthened sorting and
functional contracts. Receipt functional proofs and actual restricted index,
task and voucher certificates are checked separately. Their schemas/laws are
different: running them on the same host does not prove a new composed
index-and-receipt application invariant.

The actual Rust/Node/native byte bridge, scheduling effects, monotonic clock,
administrator sink and filesystem operations remain trusted implementation
boundaries supported by the concrete tests. The existing theorem names are not
extended to claim a complete proof of those effects. General mathematical
signed multiplication/division correctness remains outside the library's
formal claim; independent native arithmetic oracles complement its narrower
proofs. Indexed and receipt examples retain their documented principal/schema
and retention restrictions.

Persistence uses protected single-owner storage and the stated filesystem
flush/replace assumptions. It preserves the whole state, requires the exact
controller/environment on reopen, never silently reseeds or substitutes older
images, and treats possible replacement failures as fatal uncertainty.
Development data may be recreated explicitly after changes. No upgrade or
compatibility subsystem is required. Process-kill tests do not establish that
hardware honors its flush contract.

## Validation of the combined sources

All required cases passed. Evidence records preserve the two initial harness
failures and their targeted repairs; passing gates were not relabeled or
needlessly repeated.

| Gate | Completed result | Retained evidence |
| --- | --- | --- |
| `make verify-contract verify` | All four contract/general/library roots pass both official modes; eight negative controls rejected. | `evidence/verify.txt` |
| Host checks | 39 Rust tests; formatting; strict all-target Clippy; release build pass. Run by the timing implementation agent; raw host stdout was not separately retained. | Commands: `cargo test --locked`, `cargo fmt --check`, `cargo clippy --locked --all-targets -- -D warnings`. |
| Admission/runtime/service | 17 admission/verifier tests, 10 native-runtime tests and 12 real ordinary/prepared/preprocessing/scheduling/concurrency tests pass. | `evidence/initial-regression.txt` |
| Timing composition | All five real cases pass, including reversed completion, fresh identity, failed-output draining and durable reopen (74.921 s). | `evidence/timing-native.txt` |
| Optional library | Actual task certificate passes both modes; AlwaysNone/HiddenWrite rejected in both modes; 1,980 signed64 plus 1,980 collection/summary oracle cases and 250 full-content variable-length cases pass; restricted real task flow passes. | `evidence/initial-regression.txt` |
| Indexed application | Actual certificate/termination/seed and independent permission roots pass both modes; six intended full-certificate rejections and the real restricted flow pass. | `evidence/initial-feature-gate.txt` |
| Index + storage + timing | 25 real prepared/ordinary requests, independently checked persisted rows, seed-free reopen, lost handles and certificate-denial rollback pass. | `evidence/indexed-durable.json` |
| Receipts | Actual voucher and receipt functional roots pass both modes; all 43 real framed cases, including durable reopen and strong forged-receipt negatives, pass. | `evidence/voucher-repair.txt` |
| Recovery/fatal boundaries | Eight of nine recovery tests passed initially; the remaining crash test failed at socket setup before launch. After isolating the socket directory, all four SIGKILL subcases passed (99.558 s). Together all nine cases are covered, including four timing/failure subcases and lost acknowledgment/retry. | `evidence/initial-regression.txt`, `evidence/recovery-and-demo-repair.txt` |
| HTTP/inspection/demo | All five real tests pass (142.768 s), including publication, rollback, session isolation, repeated reset and startup recovery. | `evidence/recovery-and-demo-repair.txt` |
| Benchmark tooling | Eight baseline harness tests and two independent affine/direct-loop oracle tests pass; actual fixture admission, termination, seed and read-only targets pass both modes. | `evidence/baseline-harness.txt`; `benchmark/test_bench.py`; local `build/integration/benchmark-proof/`. |
| Measured requests | All 512 responses pass the independent credential/checksum oracle, chosen-executable/fresh-build equality and frozen-source checks. | `evidence/concurrency-{small,heavy}.json` and `.ndjson` |

The crash harness originally used `.build/persistence/barrier`, whose parent was
created only by the individual storage Make target. The combined fault target
uses `.build/integration/fault`, exposing that test coupling. Each crash subcase
now owns a short private `/tmp` Unix socket directory; no storage code changed.
Only the failed crash case and the deferred demo were rerun. The other eight
recovery cases already passed with the exact same fault executable.

All native/proof/performance jobs used the shared heavy-work lock. Direct fault
builds inherited the launcher's unlimited soft stack setting. The standalone
recovery target still needs that development environment, as documented in
`README.md`. No kernel fuel, source, runtime, admission rule or limit was weakened.

The new indexed durable gate independently checks exact business, index and
user rows in the saved image. It exercises maintenance/rebuild, seed-free
reopen, ephemeral handles, three actual certificate denials with unchanged
snapshots, and administrator timing while write-capable prepared handles stay
exclusive. Existing adapted omitted/forged index variants first pass ordinary
permission proofs, then fail their full consistency certificate at the intended
terminal projection obligation.

The controlled concurrent timing gate uses two distinct certified executable
paths. It proves the second queued read logged completion while the first was
still held and no response bypassed it. It also checks fresh identity after an
exclusive credential exchange and both active completions after real client
output failure, with no later queued write launch.

## Fixed-total-CPU measurement

Complete prepared-request throughput and FIFO response latency:

| Workload | One reader, median requests/s | Two readers, median requests/s | Paired throughput ratio, median (seven-pair range) | FIFO p95 latency, one / two (ms) |
| --- | ---: | ---: | ---: | ---: |
| Tiny read | 355.58 | 632.77 | 1.755× (1.514–1.799) | 22.566 / 12.894 |
| 250,000 runtime iterations | 355.08 | 616.39 | 1.734× (1.595–1.801) | 23.015 / 14.428 |
| 1,000,000 runtime iterations | 343.57 | 532.17 | 1.546× (1.456–1.829) | 25.559 / 15.805 |
| 100,000,000 runtime iterations | 74.07 | 144.96 | 1.958× (1.939–1.965) | 108.142 / 55.400 |

The tiny/250k/1m calibration remains startup-dominated. The separate 100m
follow-up adds substantial runtime computation with the **same source, proof
and executable**: 128 responses perform 12,800,000,064 logical recurrence
iterations. Its eight-request burst median is 108.004 ms versus 55.186 ms;
paired ratio MAD is 0.00663. This is complete-request measurement, not a
kernel-only timing or a count of machine instructions. Service startup and first
checked preparation are separate (10.30/10.37 seconds for the one-/two-reader
configurations). The raw `preparation_ns` includes initialization, not just
isolated proof checking or compilation.
The two services have independently generated instance-local handles.

Memory cost (MiB, one / two readers):

| Workload | Maximum sampled process-tree RSS | Maximum RSS after drained burst |
| --- | ---: | ---: |
| Tiny read | 6.340 / 10.379 | 3.527 / 7.574 |
| 250,000 runtime iterations | 6.336 / 12.504 | 3.531 / 7.574 |
| 1,000,000 runtime iterations | 6.434 / 13.059 | 3.535 / 7.574 |
| 100,000,000 runtime iterations | 6.449 / 13.543 | 3.465 / 7.590 |

**Keep the optional CPU batching implementation, with default one reader.**
The measured benefit survives a fixed CPU budget, at a clear memory cost.
These results support this narrow experiment; they do not justify changing the
default or promise the same gain for other databases and programs. A scheduler
or allocator redesign is not added to reduce that cost.

The same verified controller executable, two physical i7-11700K cores and total
native budget `--threads 2` are used with one versus two read workers. Requests
use actual opcode-3 admission, fresh authentication and normal artifact checks.
Both runtime iteration count and seed are request arguments. Every returned
credential/checksum is checked independently. There is no injected scheduling
gate, persistence or timing log during measurement.

One warmup and seven alternating paired bursts of eight requests are measured
per workload. End-to-end FIFO response latency includes queueing and delivery;
it is deliberately different from the service-time observer. Preparation/build
costs are recorded separately. Approximate 10 ms process-tree RSS sampling can
miss peaks and double-count shared pages. Drained RSS also exposes retained
controller allocation costs. The measured database is small; larger states,
mixed writes and internally parallel programs remain unmeasured.

## Source and artifact identity

Production host/protocol sources have been unchanged since the timing
integration layer. The normal controller SHA-256 is
`dd2742311f9c58c476b3182a2d3ffe1ac54e7c9ec4005490ca1aa07b4e5e791e`.
Final source hashes and the opt-in fault binary identity are recorded in the
evidence manifest. Final evidence/docs do not change the executable.

Shell Git transport lacked credentials, so the connected GitHub API was used
to create the same ordered integration commit trees and parents. Git trees
were checked for exact SHA equality and returned commit objects imported
locally. `evidence/publication-map.json` maps original local assembly commit IDs to
their byte-identical-tree published counterparts. Historical measurement
metadata is preserved, not relabeled. No force update of an existing remote
branch is needed.

The normal and fault binary hashes, concrete source hashes, gate counts and
limitations are in `evidence/source-identity.json` and `evidence/validation.json`.
`evidence/SHA256SUMS` covers every retained raw evidence file. Source-only
review found no remaining substantive implementation issue. Persistence and
idempotency cost curves, larger-state/mixed-workload performance, GPU/Bend
composition and any later main-merge decision remain outside this candidate.

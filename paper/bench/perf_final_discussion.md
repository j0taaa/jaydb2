## Trusted-base changes relative to 3f28eb7

This inventory follows the diffs of [proof/README.md](../../proof/README.md),
[SPECIFICATION.md](../../SPECIFICATION.md),
[native/SIMPLE_RUNTIME.md](../../native/SIMPLE_RUNTIME.md) and the new
[durable-storage protocol](../../docs/durable-storage.md), rather than treating
all speedups as trust-neutral. The benchmark task adds no trusted duty.

| Change on the performance branch | Trusted duty / assumption and limits | Documentation |
|---|---|---|
| Verified immutable executable images replace per-call hashes and staging-file comparisons | T1 still binds both checker acceptances, exact Book, literal C and released ELF. T3 duty 7 now trusts copying into an owned CLOEXEC memfd, installing/verifying WRITE/GROW/SHRINK/SEAL, hashing the sealed contents against the admitted receipt, and executing that exact retained fd. Staging files become diagnostic after load. Frozen public/runtime/environment inputs are still checked before future compilation; host-owned storage must remain unchanged during validation/use. Kernel seals and `/proc/self/fd` execution are explicit OS dependencies. | proof guide **T2**, **T3.7**; specification executable-integrity paragraphs; native **Identity and failures**; [task A](perf-host-images.md) |
| Pre-executed, single-use worker pool | T3 duty 4 binds each data-free child to its admitted image/runtime policy and supplies only the selected call's current root/body/registry. No child reuse or publication capability. At most eight images process-wide, including authenticator, each with one idle child/refill thread; beyond the cap or thread-start failure, spawn fresh. Reap dead children, stop/join refill and kill/reap idle children on invalidation/shutdown; release permits after cleanup. Refill hides startup latency but retains CPU/resource costs. No global memory/registration quota or readiness handshake. | proof guide **T3.4–5**; specification pool paragraphs; native **Identity and failures**, **Remaining T3 plumbing obligations**; timing **Measurement boundary**; [tasks A](perf-host-images.md)/[review fixes](perf-review-fixes.md) |
| Candidate routing plus one authoritative checked prepared worker | T3 duty 3 trusts bounded host envelope parsing only for tentative artifact location; the checked worker still authenticates against current state and selects from the latest complete registry. Host forwards original bytes unchanged, parses tag-6 metadata, compares frozen environment/raw handle/source-proof match, requires authentication readiness, and retries original checked dispatch on every doubt/failure/mismatch before publication. An artifact guard alone does not prove route completeness. Tag-0 denial equality, tag-4 identical checked selection plus T2 deterministic execution, and tag-2 fallback form the stated T2/T3 composition, not a whole-host theorem. | proof guide **T3.3, 5–7** and readiness paragraphs; specification **Optional prepared programs**; native **Checked worker path**; [task B](perf-prepared-worker-auth.md) |
| Changed principal/inspection and retry timing | Host accepts principal only with complete matching ready metadata; authenticated empty ID remains present. Candidate failure/unready metadata discards that principal and retries checked authentication; fallback authenticator principal survives a later fallback-worker crash. Prepared inspection can occur later. Tag-2 speculation can run certified pure client code the old path would not have run; its result cannot publish, but it can consume resources/delay service. Only final authoritative result/failure is visible. Pipe-thread exhaustion remains fatal after cleanup; denial transport needs those same threads. | proof guide **T3.3–6** and observer paragraphs; specification prepared retry discussion; native **Checked worker path**, **Optional administrator inspection**; [SERVICE_TIMING.md](../../tools/service/SERVICE_TIMING.md) |
| Two initialized alternating complete-state slots, one routine fdatasync | T3 physical publication/recovery now trusts exact slot framing, checksums binding sequence/length/payload, parity and consecutive sequence selection, older-slot-only writes, fatal uncertainty from attempted write onward, fdatasync before publication, and creation/growth's file fsync + replacement + directory fsync. Linux/ext4 healthy-epoch durability, device flush honesty, isolation of synced peer blocks, initialized extents, and detection of torn/mixed contents by SHA-256 are assumptions. No block/sector atomicity is assumed. Only 4096-byte f_frsize is checked; ext4 is an operator assumption. Pure crash/commit lemmas do not verify Rust/syscalls/hardware. | proof guide **Durable slots and physical assumptions**; specification **Durable host storage**; [storage protocol](../../docs/durable-storage.md); [task E/storage](perf-durable.md) |
| Strict recovery and explicit invalid-slot repair | Default recovery refuses a nonzero invalid slot unchanged. Operator repair first writes an exclusive complete evidence copy, syncs file/directory, then durably clears the peer before sequence reuse. Repair may lose the newest acknowledged commit if corruption caused the invalidity. Evidence never competes as authority and may accumulate. An all-zero newest slot cannot be distinguished from a legitimate empty peer: storage must not replace synced data with zeros. Buffered SIGKILL can tear writes. Old v1 fails closed without migration. Linux errseq can hide an already reported writeback error from a fresh open; after real sync/EIO failure, stop, preserve evidence, fix storage, reboot and assess on-disk recovery before serving. | proof guide **Durable slots and physical assumptions**; specification storage/writeback sections; storage protocol **Writeback-error recovery procedure**; [review fixes](perf-review-fixes.md) |
| memfd policy, lifetime and resource hardening | Request MFD_EXEC; fall back without it only on EINVAL for old kernels, require at least the four seals (extra F_SEAL_EXEC allowed), refuse non-executable or policy-denied images. A borrowing launch wrapper retains Image lifetime through launch/capture. Policy 2 may prevent startup. Pool caps and cleanup are physical host obligations supported by tests. | proof guide **T3.4, 7**; specification executable/pool paragraphs; native **Identity and failures**; [review fixes](perf-review-fixes.md) |

T1 checker soundness/source-purity audit and T2 official compiler/runtime
preservation remain assumptions. The dynamic loader, libc, libm, loader
configuration and inherited loader variables remain trusted, as before; memfd
seals do not cover them. Static linking and modified runtime/compiler flags
were not adopted. Exact current-root/latest-registry delivery, serial publication,
paired response delivery and admitted-program purity remain trusted plumbing.
The eight numbered T3 duties are a grouping, not a claim of eight proved host
properties or a reduced trusted base.

The checked limit-word specialization and reuse of finalization's one canonical
state encoding add **no** host duty or wire decision variant:
`LimitWords.convert_equals_reference`, `common_guard_hits` and
`Execution.finish_equals_reference` retain conversion overflow, all failure
branches and equal-root successful Commit. Single-pass framing also adds **no**
trusted premise: `TransportScan.separate_refines_reference` and
`WorkerBridge.routed_bytes_equals_original_packet` cover all inputs, including
malformed/non-octet packets. It still constructs lists and uses the generic
Value-to-State decoder. Their exact scope is documented in the proof guide,
specification/native checked-path sections and [task C](perf-finalization-c.md)
and [task D](perf-checked-entry.md). No retained checked state, compact codec,
direct typed decoder, read-only CommitReuse, host authentication or host-selected
partial-state execution is included. The checked host-denial code/memo mechanism
already existed in the baseline; it is not credited as a new speedup here.

## PostgreSQL parity and architectural floor

The E3 tables state exactly where this build stands against PostgreSQL under
the retained local durable protocol. A ratio above 1 means JayDB2 is slower.
This benchmark does not establish general PostgreSQL parity. Durable-update
rankings depend on storage synchronization that varies by session; the
work/results/security mechanisms differ, and the large-state read path still
pays complete-state costs. SQLite's lower read latency is an
unconstrained embedded baseline, not equivalent ownership enforcement.

There is no measured universal numerical latency floor. The current design
starts a **fresh checked process for every call**, sometimes ahead of selection,
then delivers and decodes a complete canonical state, validates it, authenticates
against it, runs the program, validates/finalizes and encodes complete state once,
frames output, reaps the child and publishes. Successful reads still emit
equal-root Commit and a new paired response. A ready pool moves startup out of
the interval; it does not make this a retained-state server or remove refill
work. The old unpooled dynamic hello capture was about 0.352 ms, versus an
approximately 0.042 ms historical PostgreSQL read. That empty-process diagnostic
is not a hard lower bound for a pooled selected call, and cannot be added to the
new worker timing. The measured scaling curve, rather than a guessed constant,
shows the remaining whole-state cost.

PostgreSQL also reuses an already authenticated role connection, with connection
setup outside samples; JayDB2 authenticates current credentials and resolves
the live registry inside every call. PostgreSQL/SQLite use their primary-key
indexes, while the JayDB2 point fixture retains list-based lookup. These are
properties of the retained protocol and architecture, not identical execution
or security mechanisms with a single implementation variable changed.

The measured budgets point to an architectural change for substantially
approaching PostgreSQL's small indexed-read latency and avoiding whole-state
costs as databases grow. The 65,536-byte ceiling belongs to this benchmark's
configuration; this study measures no larger configuration, and raising that
limit alone would retain the same complete-state passes. One route is a long-lived checked loop that
retains typed state and consumes serial requests, with proofs/bridges for linear
state ownership, current credentials/registry, request isolation, exact failure
and publication ordering, durability and recovery. This would abandon the
current fresh-process isolation boundary and must document the replacement.
The pinned compiler/runtime cannot simply be patched to create that service.

Another route is certified footprints/frame theorems, or a checked committed
tree with membership **and absence**, ordering/count and update witnesses,
refined to the existing logical state and laws. Host-selected rows or an
unchecked cache do not suffice; dynamic keys, branches, global credential
uniqueness, enumeration and canonical state-size checks remain obligations.
Cryptographic root commitments would add an explicit collision-resistance
assumption unless exact identity is checked otherwise. A proved index/map can
reduce linear lookup, while a direct typed/compact codec or proved unchanged-root
reuse can reduce transfer/encoding; neither by itself establishes full-state
semantic equivalence or PostgreSQL parity. Group commit could amortize durable
sync only with changed batching/publication/acknowledgement semantics. No latency
estimate for these unimplemented architectures is presented as evidence.

## Reproduction and validation scope

The exact commands for every invocation are in the raw files' `runner.command`.
The common shell pattern (one lock acquisition per invocation) is:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make -C .build/perf-final-baseline build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/perf_final.py prepared --output paper/evidence/perf-final-prepared.json'
```

`perf_final.py` requires a new output filename and refuses historical resume.
For the baseline add `--root .build/perf-final-baseline` (a detached worktree
at 3f28eb7 with its own release build and the same pinned `.tools` symlink).
Use `comparison` or `scaling` for the other experiments and distinct
`perf-final-baseline-*.json` or `perf-final-*.json` names. Scaling session1/2/3
files each preserve the original one-session layout. The generated combined
scaling files group the three independent raw sessions; they do not invent new
operation measurements. `perf_final_phases.py --output NEW.json` runs the
unchanged 100-call diagnostic capture, under the same lock/clock shell.

Builds and the original evidence pytest suite are the required validation for
this benchmark-only task; the brief explicitly waives the full make release
suite. `perf_final_report.py` additionally checks all measured outputs, warmup
and sample indices, three-session coverage, pooled/raw equivalence, update
readbacks, policy/durability probes, fixed frequency policy, source/binary
consistency and identical harness hashes. It regenerates this report's tables,
summary JSON, combined scaling files and the SVG figure. It does not replace
the old thesis evidence or update `paper/main.tex`/`paper/slides.tex`.

Exact validation outcomes, invocation wall times/log hashes, immutable baseline
evidence checks and final CPU readback are retained separately in
`perf-final-validation.json`. The CPU restoration receipt must show powersave
on every logical CPU and `intel_pstate/no_turbo=0`. Full make/proof/admission,
recovery and application suites were **not rerun in this benchmark task**;
earlier branch validation is linked above and is not represented as a new run.

Open limitations: one physical machine, warm-cache serial latency, no cold-disk,
multi-client throughput, total-memory, physical power-loss or adversarial
desktop-isolation measurements; only three independent sessions per condition;
nonrandomized E2/E3 revision order; scheduling, refill and durable-sync variation;
no current native subregion profile proving an exact additive CPU decomposition.
All completed sessions and outliers are retained. These measurements validate
observed workload results and the stated comparison, not T1–T3 or hardware
durability as formal theorems.

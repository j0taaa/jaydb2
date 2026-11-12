# Durable commit: two-slot, one-fdatasync protocol

Copied verbatim from the implementing agent report (`.build/durable/REPORT.txt` on `t3/durable-commit-log`). Protocol and trust documentation: `docs/durable-storage.md`.

```text
Branch: t3/durable-commit-log
Head: 0d21a6798fd6d464ea228ca96d1df927c47185bc
Measured runtime commit: 0d3e3d987fd37c69599aca767ceeed590ee70ca6
Measured binary SHA-256, verified against final release: a40156b1e8cb3e4db7199d5afb5fcde993499d6dadeac723350558991adf68b2

MEASUREMENTS (fixed-clock.sh, shared flock, one native worker, prepared point update, 10 rows)
Three fresh sessions per condition, 60 warmed samples per session. Every update had checked untimed readback.
Durable median: 14.491447 -> 6.861052 ms (52.65% lower)
Durable mean: 14.509555 -> 6.467361 ms
Durable p95: 16.000996 -> 7.283735 ms
Volatile median: 3.849597 -> 3.849022 ms

Session durable medians (ms):
before: 14.851677, 14.489766, 15.322973
after: 6.333659, 6.844801, 6.898191

IO BREAKDOWN
Before coordinator trace: two fsyncs combined median 11.0735 ms, mean 10.7598 ms; write+rename mean 0.048233 ms.
Final 4 KiB direct IO probe, fdatasync medians (ms): append=5.511597, preallocated=5.430765, existing=2.769674
Preallocated means unwritten allocated extents; existing means initialized data, synced before timed overwrites.
Coordinator trace confirms one fdatasync, no rename/directory fsync per routine update. Trace timings are diagnostic:
strace materially inflates round trips and has large sync outliers; all final latency figures above are untraced.
The baseline binary was built before Rust edits and is preserved as .build/durable/jaydb2-before.

PROTOCOL
Two initialized equal slots, aligned to 4096-byte filesystem blocks. Even/odd sequence parity identifies A/B.
SHA-256 covers sequence, length AND complete state image. Two valid slots must have consecutive sequences.
Overwrite only older slot frame blocks, fdatasync once, then publish/ack. Never overwrite the current latest slot.
Creation/growth use synced temp, atomic rename, directory fsync. Physical size <= two maximum padded frames.
A nonzero invalid peer is zeroed and synced at recovery before its next sequence is reused, preventing resurrection
of an earlier failed future candidate. All ambiguous valid pairs/bindings/geometries fail closed. No tail log exists.
Single-owner lock and exact immutable environment descriptor are retained. Equal-state commits reuse durable data.
Group commit could amortize the remaining sync if publication/acknowledgement were batched; the host remains serial.

TRUST ASSUMPTIONS
New required boundary: Linux/ext4 fdatasync persists data plus necessary retrieval metadata; initialized extents remain retrievable.
Writes to one aligned slot do not damage previously synced blocks in the other slot; no stale allocation contents are exposed.
SHA-256 detects torn/mixed sequence+payload contents; undetected checksum collisions are excluded. No sector/block atomicity is assumed.
Atomic rename, file/directory fsync, device flush honesty and protected storage remain required.
Unrelated media corruption, malicious rewriting and loss of acknowledged synced data remain outside the crash-only model.
A checksum is neither an authenticity/certification proof nor a formal disk-origin theorem; Rust/OS refinement remains T3.

CRASH/FAULT COVERAGE
Shared real Rust commit algorithms: before/after every prepare/write/sync and temp-write/file-sync/rename/directory-sync effect.
Every 4 KiB slot byte cut and single-byte mutation; all 3-block persistence subsets; individual persisted/missing 512-byte sectors.
New header over stale payload; stale/gapped/tied/misplaced/wrapped valid sequences; incompatible environment/limits; geometry/bounds.
Failed-future checksum resurrection through a later torn write and through partial zeroing; durable repair before sequence reuse.
Real EIO and SIGKILL: before_write, after_write, after_file_sync, before_replace, after_replace, after_directory_sync,
before_slot_write, during_slot_write, after_slot_write, before_data_sync, after_data_sync, before_publish, after_publish.
Recovery EIO/SIGKILL: before_slot_clear, during_slot_clear, after_slot_clear, after_recovery_file_sync, after_recovery_sync.
Acknowledged restart, lost receipt reply, queued dispatch termination, users/tables/credentials, handle loss, seed-free open,
owner contention, exact descriptor enforcement, corrupt/missing authority, ignored orphan temp, and growth/shrink/restart.
Process death tests do not simulate physical power loss; the byte/effect model supplies the stated crash choices.

EXACT VALIDATION COMMANDS
Every heavy invocation used: flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; <command>'
PASS: make build
PASS: make verify-contract
PASS: make verify
PASS: cargo test --locked storage::tests (11 tests)
PASS: python3 -B tools/check.py proof/DurableCommit.bend (both checkers)
PASS: make test (includes all 42 host unit tests and native/service/RLS gates)
PASS: TMPDIR="$PWD/.build/persistence/tmp" python3 -B .build/durable/growth-check.py (5 focused cases)
PASS: python3 -B .build/durable/recovery-gates.py (separately locked batch invoking the following make command)
PASS: make -k -j3 --output-sync=target test-host test-persistence test-idempotency-recovery test-recovery-integration
The last four independent targets ran concurrently inside the same held flock, using distinct binaries/databases.

EARLIER FAILURES / SKIPS
Initial benchmark startup lacked .tools; linked the installed pinned toolchain and reran. No failed-run samples are used.
Initial cargo storage compile found a 17-byte magic declared as 16; fixed before final protocol validation.
First make test-persistence was stopped after concrete 5 KB proof bindings exhausted BendTT fuel before IO.
Fixed growth fixtures to use the checked universal prepared program and require STORAGE_IO on safe failures; full rerun passed.
The focused growth rerun caught a fixture assertion that mistook retained prepared artifacts for transient staging. Fixed baseline comparison; rerun passed.
No requested final gate was skipped. Failed logs are retained as focused.log, test-persistence-failed1.log and failed-growth-*.stderr.

CPU RESTORATION
Verified scaling_governor=powersave and intel_pstate/no_turbo=0; full observation in cpu-final.json.

RAW ARTIFACTS
before-untraced/results.json; after/results.json; summary.json; before-host-traced/host-2.strace;
after-traced/host-2.strace; slot-focused.log; verify-contract.log; verify.log; test.log; growth-check.log; recovery-gates.log.
New protocol documentation: docs/durable-storage.md; checked models: proof/DurableCommit.bend and proof/Persistence.bend.
```
